import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-
  We define the game of nim as positions and moves.
  We also provide methods that determine when the game terminates and applies transitions for moves.
-/

abbrev Position : Type := List Nat

structure Move (p : Position) where
  idx    : Fin p.length
  newVal : Nat
  shrink : newVal < p.get idx

def NoMoves (p : Position) : Prop :=
  ∀ i : Fin p.length, p.get i = 0

def apply (p : Position) (m : Move p) : Position :=
  p.set m.idx.val m.newVal

/-
  We define inductive types to formalize winning strategies.
  This follows the basic idea of N and P positions under Sprague-Grundy,
    but we do not follow Sprague-Grundy that rigorously.
  A winning strategy would thus be of the Wins p type, where Wins.play gives the move.
-/

mutual
  inductive Wins : Position → Type where
    | play     : (p : Position) → (m : Move p) → Loses (apply p m) → Wins p
  inductive Loses : Position → Type where
    | noMove    : (p : Position) → NoMoves p → Loses p
    | respond  : (p : Position) → ((m : Move p) → Wins (apply p m)) → Loses p
end

/-
  We rely on nim-sum to tell us whether a position is an N or P position.
  We show that this criterion for N/P is well-defined, and then
    use `bouton` as a witness to show that there exists a strategy
    that is able to satisfy this criterion.
-/

def nimSum (p : Position) : Nat := p.foldr (· ^^^ ·) 0
def IsNPos (p : Position) : Prop := nimSum p ≠ 0
def IsPPos (p : Position) : Prop := nimSum p = 0

/- Proves that setting `l[i] <- v` changes the xor of the list to `x ↦ x ^ l[i] ^ v` -/
lemma listXorSet (l : List Nat) (i : Fin l.length) (v : Nat) :
    (l.set i.val v).foldr (· ^^^ ·) 0 = l.foldr (· ^^^ ·) 0 ^^^ l.get i ^^^ v := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    match i with
    | ⟨0, _⟩ =>
      simp [List.set, List.foldr, List.get, Nat.xor_comm]
    | ⟨n+1, h⟩ =>
      simp [List.set, List.foldr, List.get]
      rw [ih ⟨n, Nat.lt_of_succ_lt_succ h⟩]
      simp [Nat.xor_assoc]

/- Wraps listXorSet in terms of nimSum, Position, and Move. -/
lemma nimSumApply (p : Position) (m : Move p) :
    nimSum (apply p m) = nimSum p ^^^ p.get m.idx ^^^ m.newVal := by
  unfold nimSum apply
  exact listXorSet p m.idx m.newVal

/-
  Asserts that regardless of opponent's move from a P-position,
    you are guaranteed to win as the resulting position must be an N-position.
-/
theorem pposMovesToNpos (p : Position) (hP : IsPPos p) (m : Move p) :
    IsNPos (apply p m) := by
  unfold IsNPos IsPPos at *
  rw [nimSumApply, hP, Nat.zero_xor, Nat.xor_ne_zero_iff]
  exact Nat.ne_of_gt m.shrink

/- Proves that if XOR has some bit = 1, there exists an element with same bit = 1 -/
def existsTestBitOfListXor (l : List Nat) (k : Nat) (h : (l.foldr (· ^^^ ·) 0).testBit k = true) :
    { i : Fin l.length // (l.get i).testBit k = true } := by
  induction l with
  | nil => simp [List.foldr] at h
  | cons x xs ih =>
    simp only [List.foldr, Nat.testBit_xor] at h
    cases hx : x.testBit k
    · simp [hx] at h
      obtain ⟨j, hj⟩ := ih h
      exact ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, by simp [List.get]; exact hj⟩
    · exact ⟨⟨0, Nat.zero_lt_succ _⟩, by simp [List.get]; exact hx⟩

/-
  In order to show that we can turn the XOR to zero,
    we show that if the high-bit matches in some element,
    that element XOR'ed with the total XOR is smaller than the element.
-/
def xorLtOfHighBit (a s : Nat) (k : Nat) (ha : a.testBit k = true) (hs : s.testBit k = true)
    (hs_high : ∀ j, k < j → s.testBit j = false) : a ^^^ s < a := by
  apply Nat.lt_of_testBit k
  simp [Nat.testBit_xor, ha, hs]
  exact ha
  intro j hj
  simp [Nat.testBit_xor, hs_high j hj]

/-
  Wraps the two above lemmas to show that we can subtract some amount
    from some element to make the total XOR zero.
-/
def existsXorLt (l : List Nat) (hs : l.foldr (· ^^^ ·) 0 ≠ 0) :
    { i : Fin l.length // l.get i ^^^ l.foldr (· ^^^ ·) 0 < l.get i } := by
  set s := l.foldr (· ^^^ ·) 0
  set k := s.log2
  have hsk : s.testBit k = true := Nat.testBit_log2 hs
  have hs_high : ∀ j, k < j → s.testBit j = false :=
    fun j hj => Nat.testBit_lt_two_pow ((Nat.log2_lt hs).mp hj)
  obtain ⟨i, hi⟩ := existsTestBitOfListXor l k hsk
  exact ⟨i, xorLtOfHighBit (l.get i) s k hi hsk hs_high⟩

/-
  Asserts that in any N-position, there is a move into a P-position.
  Provides both a move given the position and the proof.
-/
def nposCanMoveToPpos (p : Position) (hN : IsNPos p) :
    { m : Move p // IsPPos (apply p m) } := by
  unfold IsNPos nimSum at hN
  obtain ⟨i, hi⟩ := existsXorLt p hN
  refine ⟨⟨i, p.get i ^^^ p.foldr (· ^^^ ·) 0, hi⟩, ?_⟩
  unfold IsPPos
  rw [nimSumApply]
  simp [nimSum, Nat.xor_comm]

/-
  In order to assert the strategy terminates, we demonstrate that
    the total number of stones is strictly decreasing in each move.
-/
def totalStones (p : Position) : Nat := p.sum

/- Shows that any move must decrease the sum. -/
lemma sumSetLt (l : List Nat) (i : Fin l.length) (v : Nat)
      (hv : v < l.get i) : (l.set i.val v).sum < l.sum := by
    rw [List.sum_set]
    simp [i.isLt]
    have h1 := List.sum_take_succ l i.val i.isLt
    have h2 := List.sum_take_add_sum_drop l (i.val + 1)
    simp [List.get_eq_getElem] at hv
    omega

/- Wraps the above in terms of Position and Move. -/
theorem totalStonesDecreases (p : Position) (m : Move p) :
    totalStones (apply p m) < totalStones p :=
  sumSetLt p m.idx m.newVal m.shrink

/- Implements the known winning strategy. -/
mutual
  noncomputable def strategy : (p : Position) → IsNPos p → Wins p
    | p, hN => by
      obtain ⟨m, hm⟩ := nposCanMoveToPpos p hN
      exact Wins.play p m (response (apply p m) hm)
    termination_by p _ => totalStones p
    decreasing_by exact totalStonesDecreases p m

  noncomputable def response : (p : Position) → IsPPos p → Loses p
    | p, hP => by
      by_cases h : NoMoves p
      · exact Loses.noMove p h
      · exact Loses.respond p (fun m => strategy (apply p m) (pposMovesToNpos p hP m))
    termination_by p _ => totalStones p
    decreasing_by exact totalStonesDecreases p m
end

/- We have proven that there exists a winning strategy! -/
theorem existsWinningStrategy (p : Position) (hN : IsNPos p) : Nonempty (Wins p) :=
  ⟨strategy p hN⟩
