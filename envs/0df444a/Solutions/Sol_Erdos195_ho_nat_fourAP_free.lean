-- Prove2me | solution 1 for Erdos195.ho_nat_fourAP_free
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T21:24:10.887023+00:00
-- url     : https://prove2.me/submissions/ba0ba110-74af-4501-8488-3247e332dec2

import Mathlib
import Definitions.Def_Erdos195_defs

-- Contains a port of B. S. Ho, github.com/boonsuan/4ap (MIT licence), arXiv:2609.12780.


-- ===== FourAP/Basic.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# The language of the paper

This file fixes the conventions used to formalize the paper
“A 4AP-free permutation of the positive integers”.  The construction takes place
in `ℕ`, which in Lean includes zero.  The final theorem shifts the values by one.

An arithmetic progression is expressed using the two equations
`a + c = 2 * b` and `b + d = 2 * c`.  For natural-number entries these equations,
together with `a ≠ b`, are equivalent to having a nonzero **integer** common
difference.  Thus decreasing progressions are included throughout.
-/

namespace FourAP

/-- Four consecutive terms of a nonconstant arithmetic progression, as in the
paper's main theorem. The equations avoid truncated subtraction in `ℕ`. -/
def IsAP4 (a b c d : ℕ) : Prop :=
  a ≠ b ∧ a + c = 2 * b ∧ b + d = 2 * c

/-- The equation-based representation used in this formalization is equivalent
to the paper's progression `a, a+r, a+2r, a+3r`, with a nonzero **integer**
common difference. In particular, decreasing progressions are included. -/
theorem isAP4_iff_integer_progression {a b c d : ℕ} :
    IsAP4 a b c d ↔ ∃ r : ℤ, r ≠ 0 ∧
      (b : ℤ) = (a : ℤ) + r ∧
      (c : ℤ) = (a : ℤ) + 2 * r ∧
      (d : ℤ) = (a : ℤ) + 3 * r := by
  constructor
  · rintro ⟨hne, h₁, h₂⟩
    refine ⟨(b : ℤ) - (a : ℤ), ?_, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨r, hr, hb, hc, hd⟩
    exact ⟨by omega, by omega, by omega⟩

/-- The paper's definition of a 4AP-free order, applied to a strict relation.
The relation need not be bundled as a linear order for this predicate. -/
def APFree (R : ℕ → ℕ → Prop) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, IsAP4 a b c d → R a b → R b c → R c d → False

/-- The completion `𝒞(P)` from the paragraph preceding Lemma 1, with an arbitrary
background relation `R`.  `List.idxOf` is the length of the list for a missing
entry, so the first disjunct orders the prefix and puts it before the tail. -/
def Completion (R : ℕ → ℕ → Prop) (P : List ℕ) (a b : ℕ) : Prop :=
  P.idxOf a < P.idxOf b ∨ (a ∉ P ∧ b ∉ P ∧ R a b)

/-- A safe word in the sense of the paper: a word without repetitions whose
completion is 4AP-free. The background order is made explicit here. -/
def Safe (R : ℕ → ℕ → Prop) (P : List ℕ) : Prop :=
  P.Nodup ∧ APFree (Completion R P)

end FourAP

-- ===== FourAP/Binary.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# The reverse binary order

This file formalizes the order `◁` introduced before Lemma 1 in the paper
“A 4AP-free permutation of the positive integers”.  The least significant
unequal bit decides the comparison, with `1` preceding `0`.  Dividing by two
removes a common least significant bit.  We use this recursive description
both for a computable comparison and for the elementary proofs in the paper.
-/

namespace FourAP

/-- The binary comparison from the paragraph defining `◁` in the paper.
It returns `true` precisely when the first argument precedes the second.
The special case `(0, 0)` ends the recursion after all bits have been removed. -/
def binaryCompare (a b : ℕ) : Bool :=
  if a + b = 0 then false
  else if a % 2 = b % 2 then binaryCompare (a / 2) (b / 2)
  else decide (b % 2 < a % 2)
termination_by a + b
decreasing_by omega

/-- The paper's strict order `◁`, the reverse order on binary strings when
compared at their first unequal bit starting from the least significant end. -/
def bits (a b : ℕ) : Prop := binaryCompare a b = true

/-- Binary comparison is decidable by the recursion defining the paper's order. -/
instance bitsDecidable : DecidableRel bits := fun _ _ => inferInstanceAs (Decidable (_ = true))

/-- At equal zero strings, there is no first unequal bit. -/
@[simp] theorem not_bits_zero_zero : ¬ bits 0 0 := by
  simp [bits, binaryCompare]

/-- Recursive form of the paper's definition: compare the low bits first,
then discard them if they agree. -/
theorem bits_iff (a b : ℕ) :
    bits a b ↔ b % 2 < a % 2 ∨ (a % 2 = b % 2 ∧ bits (a / 2) (b / 2)) := by
  by_cases hz : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    simp
  · unfold bits
    rw [binaryCompare]
    simp only [hz, ↓reduceIte]
    by_cases hp : a % 2 = b % 2
    · simp [hp]
    · simp [hp]

/-- Equal parity allows the rescaling described in the self-similarity
paragraph of the paper. -/
theorem bits_iff_of_same_parity {a b : ℕ} (hp : a % 2 = b % 2) :
    bits a b ↔ bits (a / 2) (b / 2) := by
  rw [bits_iff]
  simp [hp]

/-- For unequal parity, the least significant bit already decides the order. -/
theorem bits_iff_of_diff_parity {a b : ℕ} (hp : a % 2 ≠ b % 2) :
    bits a b ↔ b % 2 < a % 2 := by
  rw [bits_iff]
  simp [hp]

/-- Self-similarity of `◁` on the even integers (before Lemma 1). -/
@[simp] theorem bits_even_even (a b : ℕ) : bits (2 * a) (2 * b) ↔ bits a b := by
  rw [bits_iff]
  simp

/-- Self-similarity of `◁` on the odd integers (before Lemma 1). -/
@[simp] theorem bits_odd_odd (a b : ℕ) :
    bits (2 * a + 1) (2 * b + 1) ↔ bits a b := by
  rw [bits_iff]
  have ha : (2 * a + 1) / 2 = a := by omega
  have hb : (2 * b + 1) / 2 = b := by omega
  simp [ha, hb, Nat.add_mod]

/-- The two parity restrictions have the same rescaled order, as used in
Lemma 2. Here `p = 0` selects the even part and `p = 1` the odd part. -/
theorem bits_parity (a b p : ℕ) (hp : p < 2) :
    bits (2 * a + p) (2 * b + p) ↔ bits a b := by
  have : p = 0 ∨ p = 1 := by omega
  rcases this with rfl | rfl <;> simp

/-- All odd integers precede all even integers (the self-similarity paragraph). -/
theorem bits_odd_even (a b : ℕ) : bits (2 * a + 1) (2 * b) := by
  rw [bits_iff]
  left
  omega

/-- The converse parity comparison never holds. -/
theorem not_bits_even_odd (a b : ℕ) : ¬ bits (2 * a) (2 * b + 1) := by
  rw [bits_iff]
  omega

/-- Irreflexivity verifies that the paper's binary comparison is strict. -/
theorem bits_irrefl (a : ℕ) : ¬ bits a a := by
  by_cases ha : a = 0
  · subst a
    exact not_bits_zero_zero
  · rw [bits_iff_of_same_parity rfl]
    exact bits_irrefl (a / 2)
termination_by a
decreasing_by omega

/-- Two entries compared strictly in `◁` are different. -/
theorem bits_ne {a b : ℕ} (h : bits a b) : a ≠ b := by
  rintro rfl
  exact bits_irrefl a h

/-- Asymmetry is part of the verification that `◁` is a strict linear order. -/
theorem bits_asymm {a b : ℕ} (hab : bits a b) : ¬ bits b a := by
  have hne : a ≠ b := bits_ne hab
  rw [bits_iff] at hab ⊢
  rcases hab with hp | ⟨hp, hab⟩
  · rintro (hq | ⟨hq, _⟩) <;> omega
  · rintro (hq | ⟨_, hba⟩)
    · omega
    · exact bits_asymm hab hba
termination_by a + b
decreasing_by omega

/-- Any distinct binary strings have a first unequal bit: totality of `◁`. -/
theorem bits_total {a b : ℕ} (hne : a ≠ b) : bits a b ∨ bits b a := by
  by_cases hp : a % 2 = b % 2
  · have hq : a / 2 ≠ b / 2 := by omega
    rw [bits_iff_of_same_parity hp, bits_iff_of_same_parity hp.symm]
    exact bits_total hq
  · rw [bits_iff_of_diff_parity hp, bits_iff_of_diff_parity (Ne.symm hp)]
    omega
termination_by a + b
decreasing_by omega

/-- Transitivity completes the elementary verification that the binary
comparison in the paper defines a strict linear order. -/
theorem bits_trans {a b c : ℕ} (hab : bits a b) (hbc : bits b c) : bits a c := by
  have hne : a ≠ b := bits_ne hab
  rw [bits_iff] at hab hbc ⊢
  rcases hab with hp | ⟨hp, hab⟩
  · rcases hbc with hq | ⟨hq, _⟩
    · exact Or.inl (lt_trans hq hp)
    · left
      omega
  · rcases hbc with hq | ⟨hq, hbc⟩
    · left
      omega
    · exact Or.inr ⟨hp.trans hq, bits_trans hab hbc⟩
termination_by a + b + c
decreasing_by omega

/-- Zero cannot precede any integer, as asserted just before the discussion
of the literature in the paper. -/
theorem not_bits_zero (a : ℕ) : ¬ bits 0 a := by
  by_cases ha : a = 0
  · subst a
    exact not_bits_zero_zero
  · rw [bits_iff]
    rintro (hp | ⟨_, h⟩)
    · omega
    · exact not_bits_zero (a / 2) h
termination_by a
decreasing_by omega

/-- Zero is the greatest element of `◁` (used in Lemma 2's base case). -/
theorem bits_zero {a : ℕ} (ha : a ≠ 0) : bits a 0 := by
  rcases bits_total ha with h | h
  · exact h
  · exact False.elim (not_bits_zero a h)

/-- The elementary 3AP-freeness proof preceding equation (1). If the low bits
agree we divide all entries by two; otherwise the middle low bit differs from
both endpoint low bits, and two consecutive comparisons are impossible.
The equations include increasing and decreasing progressions alike. -/
theorem bits_no_three_of_eq {a b c : ℕ} (hap : a + c = 2 * b) :
    ¬ (bits a b ∧ bits b c) := by
  rintro ⟨hab, hbc⟩
  have hne : a ≠ b := bits_ne hab
  by_cases hp : a % 2 = b % 2
  · have hq : b % 2 = c % 2 := by omega
    have heq : a / 2 + c / 2 = 2 * (b / 2) := by omega
    exact bits_no_three_of_eq heq
      ⟨(bits_iff_of_same_parity hp).mp hab,
       (bits_iff_of_same_parity hq).mp hbc⟩
  · have hq : b % 2 ≠ c % 2 := by omega
    have h₁ := (bits_iff_of_diff_parity hp).mp hab
    have h₂ := (bits_iff_of_diff_parity hq).mp hbc
    omega
termination_by a + b + c
decreasing_by omega

/-- The dual order also contains no 3AP, as used in Lemma 1. -/
theorem bits_dual_no_three {a b c : ℕ} (hap : a + c = 2 * b) :
    ¬ (bits b a ∧ bits c b) := by
  rintro ⟨hba, hcb⟩
  exact bits_no_three_of_eq (by omega : c + a = 2 * b) ⟨hcb, hba⟩

/-- Equation (1), labelled `eq:pairs` in the paper, in equation form.
For four consecutive AP terms, the first and third adjacent pairs compare
in the same direction. The proof removes common low bits until parity differs. -/
theorem bits_pairs_of_eq {a b c d : ℕ}
    (h₁ : a + c = 2 * b) (h₂ : b + d = 2 * c) :
    bits a b ↔ bits c d := by
  by_cases hz : a + b + c + d = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    have hc : c = 0 := by omega
    have hd : d = 0 := by omega
    subst a
    subst b
    subst c
    subst d
    rfl
  · by_cases hp : a % 2 = b % 2
    · have hq : c % 2 = d % 2 := by omega
      have heq₁ : a / 2 + c / 2 = 2 * (b / 2) := by omega
      have heq₂ : b / 2 + d / 2 = 2 * (c / 2) := by omega
      rw [bits_iff_of_same_parity hp, bits_iff_of_same_parity hq]
      exact bits_pairs_of_eq heq₁ heq₂
    · have hq : c % 2 ≠ d % 2 := by omega
      rw [bits_iff_of_diff_parity hp, bits_iff_of_diff_parity hq]
      omega
termination_by a + b + c + d
decreasing_by omega

/-- Equation (1) of the paper, packaged for a nonconstant four-term AP. -/
theorem bits_pairs {a b c d : ℕ} (hap : IsAP4 a b c d) :
    bits a b ↔ bits c d := bits_pairs_of_eq hap.2.1 hap.2.2

/-- In particular the binary order itself is 4AP-free; this starts the
construction with the empty safe prefix. -/
theorem bits_apFree : APFree bits := by
  intro a b c d hap hab hbc _hcd
  exact bits_no_three_of_eq hap.2.1 ⟨hab, hbc⟩

/-- Equality of the lowest binary digits is equality of parity. This is the
bridge between the recursive definition and the binary-digit description
in the paper. -/
theorem testBit_zero_eq_iff (a b : ℕ) :
    a.testBit 0 = b.testBit 0 ↔ a % 2 = b % 2 := by
  simp only [Nat.testBit_zero, decide_eq_decide]
  omega

/-- A strict binary comparison exhibits the first unequal bit, with the
first integer's bit equal to one and the second integer's bit equal to zero.
This is the forward direction of the paper's defining description of `◁`. -/
theorem exists_first_differing_bit {a b : ℕ} (hab : bits a b) :
    ∃ k, (∀ i < k, a.testBit i = b.testBit i) ∧
      a.testBit k = true ∧ b.testBit k = false := by
  have hne : a ≠ b := bits_ne hab
  rw [bits_iff] at hab
  rcases hab with hp | ⟨hp, hab⟩
  · refine ⟨0, ?_, ?_, ?_⟩
    · intro i hi; omega
    · simp only [Nat.testBit_zero, decide_eq_true_eq]
      omega
    · simp only [Nat.testBit_zero, decide_eq_false_iff_not]
      omega
  · obtain ⟨k, hlow, ha, hb⟩ := exists_first_differing_bit hab
    refine ⟨k + 1, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact (testBit_zero_eq_iff a b).mpr hp
      | succ i =>
        simpa only [Nat.testBit_succ] using hlow i (by omega)
    · simpa only [Nat.testBit_succ] using ha
    · simpa only [Nat.testBit_succ] using hb
termination_by a + b
decreasing_by omega

/-- Conversely, the least significant unequal bit determines the recursive
comparison. This is the backward direction of the paper's definition. -/
theorem bits_of_first_differing_bit {a b k : ℕ}
    (hlow : ∀ i < k, a.testBit i = b.testBit i)
    (ha : a.testBit k = true) (hb : b.testBit k = false) : bits a b := by
  induction k generalizing a b with
  | zero =>
    rw [bits_iff]
    left
    simp only [Nat.testBit_zero, decide_eq_true_eq] at ha
    simp only [Nat.testBit_zero, decide_eq_false_iff_not] at hb
    omega
  | succ k ih =>
    have hp : a % 2 = b % 2 :=
      (testBit_zero_eq_iff a b).mp (hlow 0 (by omega))
    rw [bits_iff_of_same_parity hp]
    apply ih
    · intro i hi
      simpa only [Nat.testBit_succ] using hlow (i + 1) (by omega)
    · simpa only [Nat.testBit_succ] using ha
    · simpa only [Nat.testBit_succ] using hb

/-- The definition of `◁` in the paper, stated literally using binary digits.
There is a first differing digit, and its values are respectively `1` and `0`.
Thus our executable recursion is exactly the order described in the text. -/
theorem bits_iff_first_differing_bit (a b : ℕ) :
    bits a b ↔ ∃ k, (∀ i < k, a.testBit i = b.testBit i) ∧
      a.testBit k = true ∧ b.testBit k = false := by
  constructor
  · exact exists_first_differing_bit
  · rintro ⟨k, hlow, ha, hb⟩
    exact bits_of_first_differing_bit hlow ha hb

/-- The displayed eight-element example from the paper:
`7 ◁ 3 ◁ 5 ◁ 1 ◁ 6 ◁ 2 ◁ 4 ◁ 0`.
`Pairwise` records every comparison in this finite ordered list. -/
theorem bits_eight_example : List.Pairwise bits [7, 3, 5, 1, 6, 2, 4, 0] := by
  decide +kernel

end FourAP

-- ===== FourAP/Completion.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# Reading a finite prefix and its completion

These elementary bookkeeping facts make precise the paper's statements that
“the terms ... which lie in `P` form an initial segment” and that extending a
prefix does not move any of its old entries. They are independent of the special
binary order.
-/
namespace FourAP

variable {R : ℕ → ℕ → Prop} {P Q : List ℕ} {a b c : ℕ}

/-- The completion of a word beginning with `t`: `t` comes first, and deleting
it leaves the completion of the remaining word. This is bookkeeping for the
paper's operation of putting a finite word before the binary-ordered tail. -/
theorem completion_cons (R : ℕ → ℕ → Prop) (P : List ℕ) (t a b : ℕ) :
    Completion R (t :: P) a b ↔
      (a = t ∧ b ≠ t) ∨ (a ≠ t ∧ b ≠ t ∧ Completion R P a b) := by
  simp only [Completion, List.idxOf_cons, cond_eq_ite, beq_iff_eq, List.mem_cons]
  by_cases ha : a = t <;> by_cases hb : b = t <;> simp_all [eq_comm]

/-- In `𝒞(P)`, each entry of `P` precedes every unused integer. -/
theorem completion_mem_notMem (ha : a ∈ P) (hb : b ∉ P) :
    Completion R P a b := by
  left
  rw [List.idxOf_eq_length hb]
  exact List.idxOf_lt_length_of_mem ha

/-- On the unused integers, `𝒞(P)` agrees with the background order. -/
theorem completion_of_notMem (ha : a ∉ P) (hb : b ∉ P) :
    Completion R P a b ↔ R a b := by
  simp [Completion, ha, hb]

/-- No entry outside the prefix can precede an entry inside it. -/
theorem completion_mem_left (h : Completion R P a b) (hb : b ∈ P) : a ∈ P := by
  rcases h with h | ⟨_, hn, _⟩
  · exact List.idxOf_lt_length_iff.mp (Nat.lt_trans h (List.idxOf_lt_length_of_mem hb))
  · exact (hn hb).elim

/-- A completion is asymmetric whenever its background order is asymmetric. -/
theorem completion_asymm (hR : ∀ ⦃x y⦄, R x y → ¬ R y x)
    (h : Completion R P a b) : ¬ Completion R P b a := by
  rintro (h' | ⟨hb, ha, h'⟩)
  · rcases h with h | ⟨ha, hb, _⟩
    · omega
    · rw [List.idxOf_eq_length ha, List.idxOf_eq_length hb] at h'
      omega
  · rcases h with h | ⟨_, _, h⟩
    · rw [List.idxOf_eq_length ha, List.idxOf_eq_length hb] at h
      omega
    · exact hR h h'

/-- The completed order is irreflexive whenever the background order is.
Together with the next two lemmas, this verifies that the paper's `𝒞(P)` is
a strict linear order rather than merely a relation. -/
theorem completion_irrefl (hR : ∀ x, ¬ R x x) (a : ℕ) :
    ¬ Completion R P a a := by
  rintro (h | ⟨_, _, h⟩)
  · exact (Nat.lt_irrefl _ h)
  · exact hR a h

/-- Concatenating the finite prefix and its background-ordered complement
preserves transitivity, as required by the paper's definition of `𝒞(P)`. -/
theorem completion_trans (hR : ∀ ⦃x y z⦄, R x y → R y z → R x z)
    (hab : Completion R P a b) (hbc : Completion R P b c) :
    Completion R P a c := by
  rcases hab with hab | ⟨ha, hb, hab⟩
  · rcases hbc with hbc | ⟨hb, hc, _⟩
    · exact Or.inl (Nat.lt_trans hab hbc)
    · left
      rwa [List.idxOf_eq_length hc, ← List.idxOf_eq_length hb]
  · rcases hbc with hbc | ⟨_, hc, hbc⟩
    · have hlen : P.idxOf c ≤ P.length := List.idxOf_le_length
      rw [List.idxOf_eq_length hb] at hbc
      omega
    · exact Or.inr ⟨ha, hc, hR hab hbc⟩

/-- Every two distinct entries are comparable in `𝒞(P)` when they are
comparable in the background order. Thus the finite-prefix construction in
the paper indeed defines a strict linear order. -/
theorem completion_total (hR : ∀ ⦃x y⦄, x ≠ y → R x y ∨ R y x)
    (hne : a ≠ b) : Completion R P a b ∨ Completion R P b a := by
  by_cases ha : a ∈ P
  · by_cases hb : b ∈ P
    · have hidx : P.idxOf a ≠ P.idxOf b := fun h => hne ((List.idxOf_inj ha).mp h)
      rcases lt_or_gt_of_ne hidx with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
    · exact Or.inl (completion_mem_notMem ha hb)
  · by_cases hb : b ∈ P
    · exact Or.inr (completion_mem_notMem hb ha)
    · rcases hR hne with h | h
      · exact Or.inl (Or.inr ⟨ha, hb, h⟩)
      · exact Or.inr (Or.inr ⟨hb, ha, h⟩)

/-- Prefix extension preserves all comparisons whose first entry was already
placed. This is used twice in the contradiction argument in Lemma 2. -/
theorem completion_prefix_left (hp : P.IsPrefix Q) (ha : a ∈ P)
    (h : Completion R Q a b) : Completion R P a b := by
  obtain ⟨S, rfl⟩ := hp
  by_cases hb : b ∈ P
  · rcases h with h | ⟨hn, _, _⟩
    · left
      simpa only [List.idxOf_append, if_pos ha, if_pos hb] using h
    · exact (hn (List.mem_append_left S ha)).elim
  · exact completion_mem_notMem ha hb

/-- In an extended completion, the old word is still an initial segment. -/
theorem completion_prefix_mem_left (hp : P.IsPrefix Q) (hb : b ∈ P)
    (h : Completion R Q a b) : a ∈ P := by
  obtain ⟨S, rfl⟩ := hp
  rcases h with h | ⟨_, hn, _⟩
  · by_contra ha
    rw [List.idxOf_append, List.idxOf_append, if_neg ha, if_pos hb] at h
    have := List.idxOf_lt_length_of_mem hb
    omega
  · exact (hn (List.mem_append_left S hb)).elim

end FourAP

-- ===== FourAP/Words.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# Finite safe words

This file formalizes the parity restrictions of `𝒞(P)` used in the Extension
Lemma, and Lemma 1 (reverse binary order is safe).
The two arithmetic-progression equations used below include both increasing
and decreasing progressions.
-/

namespace FourAP

/-- The words `P₀` and `P₁` in the Extension Lemma: retain one parity and
rescale it by `2x+p ↦ x`. -/
def parityWord (p : ℕ) (P : List ℕ) : List ℕ :=
  P.filterMap (fun n => if n % 2 = p then some (n / 2) else none)

/-- Parity restriction respects the order of concatenated words, as used
when the proof forms the extension `Q = P O E`. -/
@[simp] theorem parityWord_append (p : ℕ) (P Q : List ℕ) :
    parityWord p (P ++ Q) = parityWord p P ++ parityWord p Q := by
  simp [parityWord]

/-- The recursive description of the parity-restricted word in Lemma 2. -/
@[simp] theorem parityWord_cons (p n : ℕ) (P : List ℕ) :
    parityWord p (n :: P) =
      if n % 2 = p then n / 2 :: parityWord p P else parityWord p P := by
  by_cases h : n % 2 = p <;> simp [parityWord, h]

/-- A number occurs in `Pₚ` exactly when its original, unscaled value occurs
in `P`. This is the membership assertion implicit in the parity split. -/
theorem mem_parityWord_iff {p x : ℕ} (hp : p < 2) (P : List ℕ) :
    x ∈ parityWord p P ↔ 2 * x + p ∈ P := by
  induction P with
  | nil => simp [parityWord]
  | cons n P ih =>
    rw [parityWord_cons]
    by_cases hn : n % 2 = p
    · simp only [hn, ↓reduceIte, List.mem_cons, ih]
      have hx : x = n / 2 ↔ 2 * x + p = n := by omega
      exact or_congr hx Iff.rfl
    · have hne : 2 * x + p ≠ n := by omega
      simp [hn, ih, hne]

/-- Rescaling one parity preserves distinctness; hence the parity words
appearing in the Extension Lemma are again words without repetitions. -/
theorem nodup_parityWord {p : ℕ} (hp : p < 2) {P : List ℕ}
    (hP : P.Nodup) : (parityWord p P).Nodup := by
  induction P with
  | nil => simp [parityWord]
  | cons n P ih =>
    obtain ⟨hn, hP⟩ := List.nodup_cons.mp hP
    rw [parityWord_cons]
    split_ifs with hnp
    · apply List.nodup_cons.mpr
      refine ⟨?_, ih hP⟩
      intro h
      have hh := (mem_parityWord_iff hp P).mp h
      have heq : 2 * (n / 2) + p = n := by omega
      exact hn (heq ▸ hh)
    · exact ih hP

/-- If both parity words have distinct entries, the original word does too.
This is the distinctness argument for the new word `Q = P O E` in Lemma 2. -/
theorem nodup_of_parityWord {Q : List ℕ}
    (h0 : (parityWord 0 Q).Nodup) (h1 : (parityWord 1 Q).Nodup) : Q.Nodup := by
  induction Q with
  | nil => simp
  | cons n Q ih =>
    by_cases hn : n % 2 = 0
    · have hn1 : n % 2 ≠ 1 := by omega
      rw [parityWord_cons, if_pos hn] at h0
      rw [parityWord_cons, if_neg hn1] at h1
      obtain ⟨hn0, h0⟩ := List.nodup_cons.mp h0
      apply List.nodup_cons.mpr
      refine ⟨?_, ih h0 h1⟩
      intro hmem
      apply hn0
      apply (mem_parityWord_iff (by omega : 0 < 2) Q).mpr
      have heq : 2 * (n / 2) + 0 = n := by omega
      rwa [heq]
    · have hn1 : n % 2 = 1 := by omega
      rw [parityWord_cons, if_neg hn] at h0
      rw [parityWord_cons, if_pos hn1] at h1
      obtain ⟨hn1', h1⟩ := List.nodup_cons.mp h1
      apply List.nodup_cons.mpr
      refine ⟨?_, ih h0 h1⟩
      intro hmem
      apply hn1'
      apply (mem_parityWord_iff (by omega : 1 < 2) Q).mpr
      have heq : 2 * (n / 2) + 1 = n := by omega
      rwa [heq]

/-- Restricting `𝒞(P)` to parity `p` and rescaling gives exactly `𝒞(Pₚ)`.
This formalizes the self-similarity argument in the first inductive paragraph
of the Extension Lemma. -/
theorem completion_parity {p : ℕ} (hp : p < 2) (P : List ℕ) (a b : ℕ) :
    Completion bits P (2 * a + p) (2 * b + p) ↔
      Completion bits (parityWord p P) a b := by
  induction P with
  | nil => simp [Completion, parityWord, bits_parity a b p hp]
  | cons n P ih =>
    rw [parityWord_cons]
    by_cases hn : n % 2 = p
    · rw [if_pos hn, completion_cons, completion_cons]
      have ha : 2 * a + p = n ↔ a = n / 2 := by omega
      have hb : 2 * b + p = n ↔ b = n / 2 := by omega
      simp only [Ne, ha, hb, ih]
    · have ha : 2 * a + p ≠ n := by omega
      have hb : 2 * b + p ≠ n := by omega
      simp [hn, completion_cons, ha, hb, ih]

/-- The parity words of a safe word are safe (Extension Lemma, paragraph
beginning “Both `P₀` and `P₁` are safe”). -/
theorem safe_parity {p : ℕ} (hp : p < 2) {P : List ℕ}
    (hP : Safe bits P) : Safe bits (parityWord p P) := by
  refine ⟨nodup_parityWord hp hP.1, ?_⟩
  intro a b c d hap hab hbc hcd
  apply (hP.2 : APFree (Completion bits P)) (a := 2 * a + p) (b := 2 * b + p)
    (c := 2 * c + p) (d := 2 * d + p)
  · rcases hap with ⟨hne, h₁, h₂⟩
    exact ⟨by omega, by omega, by omega⟩
  · exact (completion_parity hp P a b).mpr hab
  · exact (completion_parity hp P b c).mpr hbc
  · exact (completion_parity hp P c d).mpr hcd

/-- Normalizing a word already rescaled into parity `p` recovers the original
word, as in the construction of the suffixes `E` and `O`. -/
@[simp] theorem parityWord_map_same {p : ℕ} (hp : p < 2) (P : List ℕ) :
    parityWord p (P.map (fun x => 2 * x + p)) = P := by
  induction P with
  | nil => simp [parityWord]
  | cons x P ih =>
    simp only [List.map_cons, parityWord_cons]
    have hmod : (2 * x + p) % 2 = p := by omega
    have hdiv : (2 * x + p) / 2 = x := by omega
    simp [hmod, hdiv, ih]

/-- Projecting a word of the other parity yields the empty word. This
justifies separating the new odd and even suffixes of `Q = P O E`. -/
@[simp] theorem parityWord_map_other {p q : ℕ} (hq : q < 2)
    (hpq : p ≠ q) (P : List ℕ) :
    parityWord p (P.map (fun x => 2 * x + q)) = [] := by
  induction P with
  | nil => simp [parityWord]
  | cons x P ih =>
    simp only [List.map_cons, parityWord_cons]
    have hmod : (2 * x + q) % 2 ≠ p := by omega
    rw [if_neg hmod]
    exact ih

/-- Inside a word listed in reverse `◁` order, an earlier entry is later in
`◁`. This is the first comparison used in the two-prefix-term case of Lemma 1. -/
theorem reverse_bits_of_completion {P : List ℕ}
    (hs : P.Pairwise (fun a b => bits b a)) {a b : ℕ}
    (hab : Completion bits P a b) (hb : b ∈ P) : bits b a := by
  have hij : P.idxOf a < P.idxOf b := by
    rcases hab with h | ⟨_, hn, _⟩
    · exact h
    · exact (hn hb).elim
  have hj := List.idxOf_lt_length_of_mem hb
  have hi := hij.trans hj
  have h := (List.pairwise_iff_getElem.mp hs) (P.idxOf a) (P.idxOf b) hi hj hij
  simpa only [List.getElem_idxOf] using h

/-- **Lemma 1 of the paper.** Every finite word of distinct integers listed in
reverse `◁` order is safe. The proof separates the cases of at least three,
exactly two, and at most one progression term in the finite prefix. -/
theorem safe_of_reverse_pairwise {P : List ℕ} (hn : P.Nodup)
    (hs : P.Pairwise (fun a b => bits b a)) : Safe bits P := by
  refine ⟨hn, ?_⟩
  intro a b c d hap hab hbc hcd
  by_cases hc : c ∈ P
  · -- At least three terms lie in the reverse-ordered prefix.
    have hb := completion_mem_left hbc hc
    exact bits_dual_no_three hap.2.1
      ⟨reverse_bits_of_completion hs hab hb, reverse_bits_of_completion hs hbc hc⟩
  · have hd : d ∉ P := fun hd => hc (completion_mem_left hcd hd)
    have hcd' := (completion_of_notMem hc hd).mp hcd
    by_cases hb : b ∈ P
    · -- Exactly two terms lie in the prefix: equation (1) gives a contradiction.
      have hba := reverse_bits_of_completion hs hab hb
      exact bits_asymm hba ((bits_pairs hap).mpr hcd')
    · -- At most one term lies in the prefix, leaving a forbidden 3AP in the tail.
      have hbc' := (completion_of_notMem hb hc).mp hbc
      exact bits_no_three_of_eq hap.2.2 ⟨hbc', hcd'⟩

/-- The non-strict reverse of `◁`, used solely for sorting the finite set in
Lemma 1 and in the base case of the Extension Lemma. -/
def reverseBitsLE (a b : ℕ) : Prop := a = b ∨ bits b a

/-- The finite sorting relation in Lemma 1 has a computable comparison. -/
instance reverseBitsLEDecidable : DecidableRel reverseBitsLE :=
  fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Transitivity permits sorting in the reverse order used in Lemma 1. -/
instance reverseBitsLETrans : IsTrans ℕ reverseBitsLE where
  trans a b c hab hbc := by
    rcases hab with rfl | hab
    · exact hbc
    rcases hbc with rfl | hbc
    · exact Or.inr hab
    · exact Or.inr (bits_trans hbc hab)

/-- Antisymmetry makes the reverse listing of a finite set unique. -/
instance reverseBitsLEAntisymm : Std.Antisymm reverseBitsLE where
  antisymm a b hab hba := by
    rcases hab with h | hab
    · exact h
    rcases hba with h | hba
    · exact h.symm
    · exact (bits_asymm hab hba).elim

/-- Any two integers can be compared when forming the reverse listing. -/
instance reverseBitsLETotal : Std.Total reverseBitsLE where
  total a b := by
    by_cases h : a = b
    · exact Or.inl (Or.inl h)
    · rcases bits_total h with h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr h)

/-- List a finite set in reverse `◁` order, exactly as prescribed in Lemma 1.
This definition is computable, using mathlib's finite-set merge sort. -/
def reverseWord (T : Finset ℕ) : List ℕ := T.sort reverseBitsLE

/-- The reverse listing contains each and only each prescribed entry. -/
@[simp] theorem mem_reverseWord {T : Finset ℕ} {x : ℕ} :
    x ∈ reverseWord T ↔ x ∈ T := Finset.mem_sort reverseBitsLE

/-- The reverse listing contains no repeated entry, as required of a word. -/
theorem reverseWord_nodup (T : Finset ℕ) : (reverseWord T).Nodup :=
  Finset.sort_nodup T reverseBitsLE

/-- The reverse listing has the strict reverse order required in Lemma 1. -/
theorem reverseWord_pairwise (T : Finset ℕ) :
    (reverseWord T).Pairwise (fun a b => bits b a) := by
  apply List.Pairwise.imp₂ (R := reverseBitsLE) (S := (· ≠ ·))
    (fun _ _ h hne => h.resolve_left hne)
  · exact Finset.pairwise_sort T reverseBitsLE
  · exact reverseWord_nodup T

/-- Lemma 1 specialized to the canonical reverse listing of a finite set. -/
theorem safe_reverseWord (T : Finset ℕ) : Safe bits (reverseWord T) :=
  safe_of_reverse_pairwise (reverseWord_nodup T) (reverseWord_pairwise T)

/-- If zero belongs to a finite set, its reverse binary listing begins with
zero. This is the sorting observation in the base case of Lemma 2. -/
theorem reverseWord_zero_first {T : Finset ℕ} (h0 : 0 ∈ T) :
    reverseWord T = 0 :: reverseWord (T.erase 0) := by
  have hsort := Finset.sort_insert (s := T.erase 0) reverseBitsLE
    (a := 0) (fun b hb => Or.inr (bits_zero (Finset.mem_erase.mp hb).1))
    (by simp : 0 ∉ T.erase 0)
  simpa only [Finset.insert_erase h0, reverseWord] using hsort

/-- Canonical form of the base-case extension in Lemma 2. Sorting `P ∪ T`
in reverse binary order preserves the old prefix whenever all its entries
are zero. This also connects the executable construction to the proof. -/
theorem reverseWord_union_prefix {P : List ℕ} (hP : P.Nodup)
    (hzero : ∀ x ∈ P, x = 0) (T : Finset ℕ) :
    P.IsPrefix (reverseWord (P.toFinset ∪ T)) := by
  cases P with
  | nil => exact List.nil_prefix
  | cons x P =>
    have hx : x = 0 := hzero x (by simp)
    subst x
    have hnil : P = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have hx0 : x = 0 := hzero x (by simp [hx])
      subst x
      exact (List.nodup_cons.mp hP).1 hx
    subst P
    rw [reverseWord_zero_first (by simp : 0 ∈ ([0] : List ℕ).toFinset ∪ T)]
    exact ⟨reverseWord ((([0] : List ℕ).toFinset ∪ T).erase 0), rfl⟩


end FourAP

-- ===== FourAP/Splice.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# The contradiction at the heart of Lemma 2

The last half of the extension lemma needs only three facts about the new
completion: the old prefix remains fixed, each parity restriction is 4AP-free,
and the odd-before-even comparison in equation (2) holds. We isolate this
argument so that the subsequent recursive construction can be read separately
from its safety proof.
-/
namespace FourAP

/-- Lemma 2, from “Suppose, for a contradiction, that a 4AP ...” to the end.
`hparity` excludes progressions with even common difference. `hguard` is exactly
the displayed odd-before-even property labelled `eq:odd-even` in the paper. -/
theorem safe_of_parity_and_guard {P Q : List ℕ}
    (hP : Safe bits P) (hp : P.IsPrefix Q) (hq : Q.Nodup)
    (hparity : ∀ ⦃a b c d : ℕ⦄, IsAP4 a b c d → a % 2 = b % 2 →
      Completion bits Q a b → Completion bits Q b c → Completion bits Q c d → False)
    (hguard : ∀ ⦃x y : ℕ⦄, x ∉ P → y ∉ P → x % 2 = 0 → y % 2 = 1 →
      y ≤ 2 * x → Completion bits Q y x) :
    Safe bits Q := by
  refine ⟨hq, ?_⟩
  intro a b c d hap hab hbc hcd
  by_cases heven : a % 2 = b % 2
  · exact hparity hap heven hab hbc hcd
  have heq₁ := hap.2.1
  have heq₂ := hap.2.2
  -- If the third term was already placed, all three old comparisons survive.
  have hc : c ∉ P := by
    intro hc
    have hb := completion_prefix_mem_left hp hc hbc
    have ha := completion_prefix_mem_left hp hb hab
    exact hP.2 hap (completion_prefix_left hp ha hab)
      (completion_prefix_left hp hb hbc) (completion_prefix_left hp hc hcd)
  have hd : d ∉ P := fun hd => hc (completion_prefix_mem_left hp hd hcd)
  by_cases hcEven : c % 2 = 0
  · -- Paper: `d = 2c - b ≤ 2c`, so the guard puts `d` before `c`.
    have hdOdd : d % 2 = 1 := by omega
    have hdc := hguard hc hd hcEven hdOdd (by omega)
    exact completion_asymm (R := bits) (fun {_ _} h => bits_asymm h) hcd hdc
  · have hcOdd : c % 2 = 1 := by omega
    have hbEven : b % 2 = 0 := by omega
    have hdEven : d % 2 = 0 := by omega
    -- If `b` was old, the odd-even tail comparison already gives an AP in 𝒞(P).
    have hb : b ∉ P := by
      intro hb
      have ha := completion_prefix_mem_left hp hb hab
      have hcdOld : Completion bits P c d := by
        apply (completion_of_notMem hc hd).2
        rw [bits_iff_of_diff_parity (by omega : c % 2 ≠ d % 2)]
        omega
      exact hP.2 hap (completion_prefix_left hp ha hab)
        (completion_mem_notMem hb hc) hcdOld
    -- Paper: `c = 2b - a ≤ 2b`, giving the remaining contradiction.
    have hcb := hguard hb hc hbEven hcOdd (by omega)
    exact completion_asymm (R := bits) (fun {_ _} h => bits_asymm h) hbc hcb

end FourAP

-- ===== FourAP/Glue.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# Joining the odd and even extensions

This file formalizes the middle part of the proof of Lemma 2 in the paper
“A 4AP-free permutation of the positive integers”: after extending the two
parity words, put the new odd entries before the new even entries.

The suffixes `O` and `E` in the statements below are normalized: their entries
are rescaled by `x ↦ 2x+1` and `x ↦ 2x` when appended to the old word `P`.
The guard on the odd target set is exactly the paper's requirement that all
normalized odd entries below `h` have been included.
-/

namespace FourAP

/-- Putting further entries after a finite word preserves the fact that each
entry of that word precedes each entry outside it.  This is the comparison
between the new odd block and the new even block in Lemma 2. -/
theorem completion_append_before {R : ℕ → ℕ → Prop} {A B : List ℕ}
    {y x : ℕ} (hy : y ∈ A) (hx : x ∉ A) : Completion R (A ++ B) y x := by
  apply Or.inl
  rw [List.idxOf_append, List.idxOf_append, if_pos hy, if_neg hx]
  have := List.idxOf_lt_length_of_mem hy
  omega

/-- **Lemma 2, construction of `Q = P O E` and its safety.**

The two recursive calls have already provided safe extensions of `P₀` and
`P₁`.  The even bound `h` determines how many odd entries must be included.
First we identify the parity restrictions of the new completion, then prove
the odd-before-even comparison displayed as equation (2) in the paper.
The final arithmetic-progression contradiction is `safe_of_parity_and_guard`.
-/
theorem safe_splice {P E O : List ℕ}
    (hP : Safe bits P)
    (hE : Safe bits (parityWord 0 P ++ E))
    (hO : Safe bits (parityWord 1 P ++ O))
    (h : ℕ) (hbound : ∀ e ∈ E, 2 * e ≤ h)
    (hcover : ∀ k < h, k ∈ parityWord 1 P ++ O) :
    Safe bits (P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0)) := by
  let Q := P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0)
  have h0 : parityWord 0 Q = parityWord 0 P ++ E := by
    simp only [Q, parityWord_append,
      parityWord_map_other (by decide : 1 < 2) (by decide : 0 ≠ 1),
      parityWord_map_same (by decide : 0 < 2), List.append_nil]
  have h1 : parityWord 1 Q = parityWord 1 P ++ O := by
    simp only [Q, parityWord_append,
      parityWord_map_same (by decide : 1 < 2),
      parityWord_map_other (by decide : 0 < 2) (by decide : 1 ≠ 0),
      List.append_nil]
  have hsafe (p : ℕ) (hp : p < 2) : Safe bits (parityWord p Q) := by
    have : p = 0 ∨ p = 1 := by omega
    rcases this with rfl | rfl
    · rwa [h0]
    · rwa [h1]
  apply safe_of_parity_and_guard hP
  · exact ⟨O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0),
      (List.append_assoc ..).symm⟩
  · exact nodup_of_parityWord (hsafe 0 (by decide)).1 (hsafe 1 (by decide)).1
  · -- An even common difference keeps all four terms in one parity.
    intro a b c d hap hp hab hbc hcd
    let p := a % 2
    have hp2 : p < 2 := Nat.mod_lt _ (by decide)
    have ha : a = 2 * (a / 2) + p := by omega
    have hb : b = 2 * (b / 2) + p := by omega
    have hc : c = 2 * (c / 2) + p := by
      have := hap.2.1
      omega
    have hd : d = 2 * (d / 2) + p := by
      have := hap.2.2
      omega
    have hap' : IsAP4 (a / 2) (b / 2) (c / 2) (d / 2) := by
      rcases hap with ⟨hne, h₁, h₂⟩
      exact ⟨by omega, by omega, by omega⟩
    apply (hsafe p hp2).2 hap'
    · apply (completion_parity hp2 Q (a / 2) (b / 2)).mp
      simpa only [← ha, ← hb] using hab
    · apply (completion_parity hp2 Q (b / 2) (c / 2)).mp
      simpa only [← hb, ← hc] using hbc
    · apply (completion_parity hp2 Q (c / 2) (d / 2)).mp
      simpa only [← hc, ← hd] using hcd
  · -- Equation (2): an unplaced odd `y ≤ 2x` must precede an unplaced even `x`.
    intro x y hxP hyP hxEven hyOdd hyx
    have hxO : x ∉ O.map (fun z => 2 * z + 1) := by
      rintro hx
      obtain ⟨z, _, hz⟩ := List.mem_map.mp hx
      omega
    by_cases hxQ : x ∈ Q
    · -- If `x` is a new even entry, the odd target has already captured `y`.
      have hxE : x ∈ E.map (fun z => 2 * z + 0) := by
        simpa only [Q, List.mem_append, hxP, hxO, false_or] using hxQ
      obtain ⟨e, he, hex⟩ := List.mem_map.mp hxE
      have hxh : x ≤ h := by have := hbound e he; omega
      have hyrepr : 2 * (y / 2) + 1 = y := by omega
      have hymem := hcover (y / 2) (by omega)
      have hyO : y / 2 ∈ O := by
        rcases List.mem_append.mp hymem with hyold | hynew
        · have hyold' := (mem_parityWord_iff (by decide : 1 < 2) P).mp hyold
          exact (hyP (hyrepr ▸ hyold')).elim
        · exact hynew
      have hyMapped : y ∈ O.map (fun z => 2 * z + 1) :=
        List.mem_map.mpr ⟨y / 2, hyO, hyrepr⟩
      exact completion_append_before
        (List.mem_append_right P hyMapped)
        (by simpa only [List.mem_append, not_or] using And.intro hxP hxO)
    · -- An unused even entry follows all odd entries, both placed and unused.
      by_cases hyQ : y ∈ Q
      · exact completion_mem_notMem hyQ hxQ
      · apply (completion_of_notMem hyQ hxQ).mpr
        rw [bits_iff_of_diff_parity (by omega : y % 2 ≠ x % 2)]
        omega

end FourAP

-- ===== FourAP/Extension.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# Lemma 2: the executable extension of a safe word

This file formalizes the Extension Lemma in the paper
“A 4AP-free permutation of the positive integers”. The recursive function
`extendAlgorithm` follows the choices in the paper's proof: extend the even
part first, then extend the odd part to cover the required initial interval,
and append the odd suffix before the even suffix. In the base case, list the
union of the old word and the target set in reverse binary order.

The recursion terminates because each parity projection has a strictly smaller
largest entry. `extendAlgorithm_spec` proves its safety, prefix preservation,
and target coverage in one induction. The paper's existential Lemma 2 is the
immediate corollary `safe_extend`.
-/

namespace FourAP

/-- The normalized parity-`p` elements of the target set in Lemma 2.
For `p = 0` this divides the even targets by two; for `p = 1` it sends an
odd target `t` to `(t-1)/2`, equivalently `t/2` in natural-number division. -/
def parityTarget (p : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (T.filter (fun t => t % 2 = p)).image (fun t => t / 2)

/-- Every target of the selected parity contributes its normalized value,
as required by the recursive calls in Lemma 2. -/
theorem div_mem_parityTarget {p t : ℕ} {T : Finset ℕ}
    (ht : t ∈ T) (hp : t % 2 = p) : t / 2 ∈ parityTarget p T :=
  Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hp⟩, rfl⟩

/-- The induction measure in Lemma 2 decreases after either parity
projection, provided the old word has a positive largest entry. -/
theorem parityWord_max_lt {P : List ℕ} {p : ℕ} (hp : p < 2)
    (hm : 0 < P.toFinset.sup id) :
    (parityWord p P).toFinset.sup id < P.toFinset.sup id := by
  apply (Finset.sup_lt_iff hm).mpr
  intro x hx
  have hxP : 2 * x + p ∈ P :=
    (mem_parityWord_iff hp P).mp (by simpa using hx)
  have hle : 2 * x + p ≤ P.toFinset.sup id :=
    Finset.le_sup (f := id) (by simpa using hxP)
  dsimp
  omega

/-- An insertion-sort implementation of the reverse listing in Lemma 1.
It is extensionally identical to `reverseWord`; using structural insertion
sort also allows the displayed numerical example to reduce in Lean's kernel. -/
def reverseWordExecutable (T : Finset ℕ) : List ℕ :=
  Quot.liftOn T.val (List.insertionSort reverseBitsLE) fun l₁ l₂ h =>
    ((List.perm_insertionSort reverseBitsLE l₁).trans
      (h.trans (List.perm_insertionSort reverseBitsLE l₂).symm)).eq_of_pairwise'
        (List.pairwise_insertionSort reverseBitsLE l₁)
        (List.pairwise_insertionSort reverseBitsLE l₂)

/-- The executable reverse listing is the same canonical word as in Lemma 1;
the choice of sorting algorithm does not change the paper's construction. -/
@[simp] theorem reverseWordExecutable_eq (T : Finset ℕ) :
    reverseWordExecutable T = reverseWord T := by
  rcases T with ⟨s, hs⟩
  induction s using Quot.inductionOn with
  | h l => exact (List.mergeSort_eq_insertionSort reverseBitsLE l).symm

/-- An executable form of **Lemma 2 (Extension)**, using exactly the choices
in its proof. `E` and `O` are normalized suffixes, so the final maps restore
their original parity. In the base case the union of prefix and target is
listed without repetition in reverse `◁` order, as in Lemma 1. -/
def extendAlgorithm (P : List ℕ) (T : Finset ℕ) : List ℕ :=
  if _hm : P.toFinset.sup id = 0 then reverseWordExecutable (P.toFinset ∪ T)
  else
    let P₀ := parityWord 0 P
    let P₁ := parityWord 1 P
    let Q₀ := extendAlgorithm P₀ (parityTarget 0 T)
    let E := Q₀.drop P₀.length
    let h := (E.map (fun x => 2 * x + 0)).toFinset.sup id
    let Q₁ := extendAlgorithm P₁ (parityTarget 1 T ∪ Finset.range h)
    let O := Q₁.drop P₁.length
    P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0)
termination_by P.toFinset.sup id
decreasing_by
  · exact parityWord_max_lt (by decide) (by omega)
  · exact parityWord_max_lt (by decide) (by omega)

/-- The specification asserted in Lemma 2: a safe extension, preserving the
old prefix and containing every prescribed target. This predicate packages
the three conclusions without hiding the actual output word. -/
def ExtensionResult (P : List ℕ) (T : Finset ℕ) (Q : List ℕ) : Prop :=
  Safe bits Q ∧ P.IsPrefix Q ∧ ∀ t ∈ T, t ∈ Q

/-- Splitting off the newly appended suffix recovers the entire extension.
This is the list identity used when the paper introduces `E` and `O`. -/
theorem prefix_append_drop {P Q : List ℕ} (h : P.IsPrefix Q) :
    P ++ Q.drop P.length = Q := by
  rw [List.prefix_iff_eq_take.mp h]
  simpa only [List.length_take, min_eq_left h.length_le] using
    List.take_append_drop P.length Q

/-- Correctness of the executable Extension Lemma. This follows the paper's
induction literally; `safe_splice` contains its odd-before-even argument. -/
theorem extendAlgorithm_spec (P : List ℕ) (T : Finset ℕ) (hP : Safe bits P) :
    ExtensionResult P T (extendAlgorithm P T) := by
  rw [extendAlgorithm]
  split_ifs with hm
  · rw [reverseWordExecutable_eq]
    refine ⟨safe_reverseWord _, reverseWord_union_prefix hP.1 ?_ T, ?_⟩
    · intro x hx
      have hxle : x ≤ P.toFinset.sup id :=
        Finset.le_sup (f := id) (by simpa using hx)
      omega
    · intro t ht
      exact mem_reverseWord.mpr (Finset.mem_union_right _ ht)
  · let P₀ := parityWord 0 P
    let P₁ := parityWord 1 P
    let Q₀ := extendAlgorithm P₀ (parityTarget 0 T)
    let E := Q₀.drop P₀.length
    let h := (E.map (fun x => 2 * x + 0)).toFinset.sup id
    let Q₁ := extendAlgorithm P₁ (parityTarget 1 T ∪ Finset.range h)
    let O := Q₁.drop P₁.length
    have h₀ := extendAlgorithm_spec P₀ (parityTarget 0 T) (safe_parity (by decide) hP)
    have h₁ := extendAlgorithm_spec P₁ (parityTarget 1 T ∪ Finset.range h)
      (safe_parity (by decide) hP)
    change ExtensionResult P₀ (parityTarget 0 T) Q₀ at h₀
    change ExtensionResult P₁ (parityTarget 1 T ∪ Finset.range h) Q₁ at h₁
    have heq₀ : P₀ ++ E = Q₀ := prefix_append_drop h₀.2.1
    have heq₁ : P₁ ++ O = Q₁ := prefix_append_drop h₁.2.1
    change ExtensionResult P T
      (P ++ O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0))
    refine ⟨?_, ?_, ?_⟩
    · apply safe_splice (h := h) hP
      · change Safe bits (P₀ ++ E)
        rw [heq₀]
        exact h₀.1
      · change Safe bits (P₁ ++ O)
        rw [heq₁]
        exact h₁.1
      · intro e he
        have he' : 2 * e + 0 ∈ E.map (fun x => 2 * x + 0) := List.mem_map.mpr ⟨e, he, rfl⟩
        exact Finset.le_sup (f := id) (by simpa using he')
      · intro k hk
        rw [heq₁]
        exact h₁.2.2 k (Finset.mem_union_right _ (Finset.mem_range.mpr hk))
    · exact ⟨O.map (fun x => 2 * x + 1) ++ E.map (fun x => 2 * x + 0),
        (List.append_assoc ..).symm⟩
    · intro t ht
      have hp : t % 2 = 0 ∨ t % 2 = 1 := by omega
      rcases hp with hp | hp
      · have ht₀ := h₀.2.2 (t / 2) (div_mem_parityTarget ht hp)
        rw [← heq₀] at ht₀
        rcases List.mem_append.mp ht₀ with htP | htE
        · have hmem := (mem_parityWord_iff (by decide : 0 < 2) P).mp htP
          have heq : 2 * (t / 2) + 0 = t := by omega
          exact List.mem_append_left _ (List.mem_append_left _ (heq ▸ hmem))
        · apply List.mem_append_right
          exact List.mem_map.mpr ⟨t / 2, htE, by omega⟩
      · have ht₁ := h₁.2.2 (t / 2)
          (Finset.mem_union_left _ (div_mem_parityTarget ht hp))
        rw [← heq₁] at ht₁
        rcases List.mem_append.mp ht₁ with htP | htO
        · have hmem := (mem_parityWord_iff (by decide : 1 < 2) P).mp htP
          have heq : 2 * (t / 2) + 1 = t := by omega
          exact List.mem_append_left _ (List.mem_append_left _ (heq ▸ hmem))
        · apply List.mem_append_left
          apply List.mem_append_right
          exact List.mem_map.mpr ⟨t / 2, htO, by omega⟩
termination_by P.toFinset.sup id
decreasing_by
  · exact parityWord_max_lt (by decide) (by omega)
  · exact parityWord_max_lt (by decide) (by omega)

/-- **Lemma 2 (Extension) of the paper.** Every safe finite word is an initial
segment of a safe finite word containing any prescribed finite target set.
The witness is the executable word constructed and verified above. -/
theorem safe_extend (P : List ℕ) (hP : Safe bits P) (T : Finset ℕ) :
    ∃ Q, Safe bits Q ∧ P.IsPrefix Q ∧ ∀ t ∈ T, t ∈ Q :=
  ⟨extendAlgorithm P T, extendAlgorithm_spec P T hP⟩

end FourAP

-- ===== FourAP/Limit.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# A computable permutation from safe stages

This file gives the effective version of the last proof and the computability
remark in the paper “A 4AP-free permutation of the positive integers”.
Given computable increasing safe words `P n` containing all integers below
`n`, both directions of the resulting permutation are computable:

* To find the value at position `i`, read position `i` in `P (i + 1)`.
* To find the position of a value `t`, find `t` in `P (t + 1)`.

These bounds are sufficient, but not necessarily efficient.  The theorem
`permutationOfSafeStages_eq_getElem` justifies the more efficient prescription
in the paper's remark: stop at *any* stage long enough to contain the position.
Neither direction of the equivalence uses a choice of preimage.
-/

namespace FourAP

/-- The conclusion of the paper for a sequence indexed by `ℕ`: no four entries
at increasing positions form a nonconstant arithmetic progression.  Because
`IsAP4` uses equations rather than natural subtraction, decreasing arithmetic
progressions are excluded as well. -/
def SequenceAPFree (f : ℕ → ℕ) : Prop :=
  ∀ ⦃i j k l : ℕ⦄, i < j → j < k → k < l →
    ¬ IsAP4 (f i) (f j) (f k) (f l)

/-- Once one stage is a prefix of its successor, it is a prefix of every
later stage. This is the “No entry, once placed, is ever moved” assertion in
the final proof of the paper. -/
theorem safeStages_prefix (P : ℕ → List ℕ)
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1))) {m n : ℕ} (hmn : m ≤ n) :
    (P m).IsPrefix (P n) := by
  induction hmn with
  | refl => exact List.prefix_refl _
  | @step n hmn ih => exact ih.trans (hstep n)

/-- Exhaustive targets give a concrete length bound: a word containing
`0, …, n-1` has at least `n` entries. Thus every requested position can be
reached after a bounded number of stages in the computability remark. -/
theorem safeStages_length (P : ℕ → List ℕ)
    (hcover : ∀ n t, t < n → t ∈ P n) (n : ℕ) : n ≤ (P n).length := by
  have hsub : List.range n ⊆ P n := by
    intro t ht
    exact hcover n t (List.mem_range.mp ht)
  simpa using (List.nodup_range (n := n)).length_le_of_subset hsub

/-- Reading a position at the bounded stage `i + 1` gives the same value as
reading it at any stage where it is already present. This is the finite-stage
stabilization argument underlying the computational procedure in the remark. -/
theorem safeStages_value_eq_getElem (P : ℕ → List ℕ)
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n)
    (n i : ℕ) (hi : i < (P n).length) : (P (i + 1)).getD i 0 = (P n)[i] := by
  have hi' : i < (P (i + 1)).length :=
    lt_of_lt_of_le (Nat.lt_succ_self i) (safeStages_length P hcover (i + 1))
  rw [List.getD_eq_getElem _ _ hi']
  let N := max n (i + 1)
  have h₁ : (P (i + 1)).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_right _ _)
  have h₂ : (P n).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_left _ _)
  exact (h₁.getElem hi').trans (h₂.getElem hi).symm

/-- A value has the same position in every stage in which it occurs.
This is the inverse form of the paper's assertion that placed entries never
move, and makes the inverse permutation computable without choosing preimages. -/
theorem safeStages_idxOf_eq (P : ℕ → List ℕ)
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n)
    (n t : ℕ) (ht : t ∈ P n) : (P (t + 1)).idxOf t = (P n).idxOf t := by
  let N := max n (t + 1)
  have h₁ : (P (t + 1)).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_right _ _)
  have h₂ : (P n).IsPrefix (P N) :=
    safeStages_prefix P hstep (Nat.le_max_left _ _)
  exact (h₁.idxOf_eq_of_mem (hcover _ _ (Nat.lt_succ_self t))).trans
    (h₂.idxOf_eq_of_mem ht).symm

/-- The actual computable equivalence constructed by the final proof of the
paper from computable safe stages. Its forward map reads a bounded stage,
and its inverse searches a bounded finite word; the proofs below verify
that these explicitly given maps are mutually inverse. -/
def permutationOfSafeStages (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) : ℕ ≃ ℕ where
  toFun i := (P (i + 1)).getD i 0
  invFun t := (P (t + 1)).idxOf t
  left_inv i := by
    dsimp only
    have hi : i < (P (i + 1)).length :=
      lt_of_lt_of_le (Nat.lt_succ_self i) (safeStages_length P hcover (i + 1))
    have hvalue := safeStages_value_eq_getElem P hstep hcover (i + 1) i hi
    have hmem : (P (i + 1)).getD i 0 ∈ P (i + 1) := by
      rw [hvalue]
      exact List.getElem_mem hi
    rw [safeStages_idxOf_eq P hstep hcover (i + 1) _ hmem, hvalue]
    exact (hsafe (i + 1)).1.idxOf_getElem i hi
  right_inv t := by
    have ht : t ∈ P (t + 1) := hcover _ _ (Nat.lt_succ_self t)
    have hi := List.idxOf_lt_length_iff.mpr ht
    exact (safeStages_value_eq_getElem P hstep hcover (t + 1) _ hi).trans
      (List.getElem_idxOf hi)

/-- The bounded evaluation rule for the forward permutation in the paper's
computability remark. Coverage proves that the default value is never used. -/
@[simp] theorem permutationOfSafeStages_apply
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) (i : ℕ) :
    permutationOfSafeStages R P hsafe hstep hcover i = (P (i + 1)).getD i 0 := rfl

/-- The inverse permutation is a finite search in the stage that is
guaranteed to contain the value. This strengthens the computability remark
by supplying an explicit inverse as well as an explicit forward map. -/
@[simp] theorem permutationOfSafeStages_symm_apply
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) (t : ℕ) :
    (permutationOfSafeStages R P hsafe hstep hcover).symm t = (P (t + 1)).idxOf t := rfl

/-- The precise stopping rule from the paper's remark: the value at position
`i` can be read from any finite stage whose length is greater than `i`.
Later stages have exactly the same entry at that position. -/
theorem permutationOfSafeStages_eq_getElem
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n)
    (n i : ℕ) (hi : i < (P n).length) :
    permutationOfSafeStages R P hsafe hstep hcover i = (P n)[i] :=
  safeStages_value_eq_getElem P hstep hcover n i hi

/-- The finite-stage contradiction in the last proof of the paper, applied
to the explicitly computable permutation. All four entries of a hypothetical
progression lie in a single safe stage, where their positions give the same
three comparisons in the completion. -/
theorem permutationOfSafeStages_apFree
    (R : ℕ → ℕ → Prop) (P : ℕ → List ℕ)
    (hsafe : ∀ n, Safe R (P n))
    (hstep : ∀ n, (P n).IsPrefix (P (n + 1)))
    (hcover : ∀ n t, t < n → t ∈ P n) :
    SequenceAPFree (permutationOfSafeStages R P hsafe hstep hcover) := by
  intro i j k l hij hjk hkl hap
  let f := permutationOfSafeStages R P hsafe hstep hcover
  let N := l + 1
  have hl : l < (P N).length :=
    lt_of_lt_of_le (Nat.lt_succ_self l) (safeStages_length P hcover N)
  have hk : k < (P N).length := Nat.lt_trans hkl hl
  have hj : j < (P N).length := Nat.lt_trans hjk hk
  have hi : i < (P N).length := Nat.lt_trans hij hj
  have hidx (x : ℕ) (hx : x < (P N).length) : (P N).idxOf (f x) = x := by
    rw [permutationOfSafeStages_eq_getElem R P hsafe hstep hcover N x hx]
    exact (hsafe N).1.idxOf_getElem x hx
  apply (hsafe N).2 hap
  · apply Or.inl
    change (P N).idxOf (f i) < (P N).idxOf (f j)
    simpa only [hidx i hi, hidx j hj] using hij
  · apply Or.inl
    change (P N).idxOf (f j) < (P N).idxOf (f k)
    simpa only [hidx j hj, hidx k hk] using hjk
  · apply Or.inl
    change (P N).idxOf (f k) < (P N).idxOf (f l)
    simpa only [hidx k hk, hidx l hl] using hkl

end FourAP

-- ===== FourAP/Construction.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# The permutation of the positive integers

This file formalizes the final proof and computability remark in the paper
“A 4AP-free permutation of the positive integers”. Starting from the empty
word, stage `n + 1` extends stage `n` with target `{n}`. These safe words give
an explicit bijection of `ℕ`, proved 4AP-free by `permutationOfSafeStages_apFree`.
Adding one to each value gives the positive sequence; shifting the positions
as well gives the positive permutation in the paper's indexing convention.

The numerical prefixes from the remark are checked separately in
`FourAP.Examples`, using the stabilization results proved here.
-/

namespace FourAP

/-- The initial stage `P⁽⁰⁾ = []` in the final proof is safe, since its
completion is the 3AP-free binary order. -/
theorem empty_safe : Safe bits [] := by
  constructor
  · simp
  · simpa [APFree, Completion] using bits_apFree

/-- The singleton-target stages `P⁽ⁿ⁾` from the proof of the theorem and the
final remark: start empty, then force `0`, `1`, `2`, ... in succession. -/
def algorithmStage : ℕ → List ℕ
  | 0 => []
  | n + 1 => extendAlgorithm (algorithmStage n) {n}

/-- Every stage of the executable construction is safe, as asserted in the
proof of the main theorem. -/
theorem algorithmStage_safe (n : ℕ) : Safe bits (algorithmStage n) := by
  induction n with
  | zero => simpa only [algorithmStage] using empty_safe
  | succ n ih => exact (extendAlgorithm_spec _ _ ih).1

/-- The executable stages retain every entry already placed (main proof). -/
theorem algorithmStage_prefix (n : ℕ) :
    (algorithmStage n).IsPrefix (algorithmStage (n + 1)) :=
  (extendAlgorithm_spec _ _ (algorithmStage_safe n)).2.1

/-- By stage `n`, all integers below `n` have appeared. This supplies the
exhaustion statement in the main proof and the termination guarantee in the
final remark's procedure for computing any given entry. -/
theorem algorithmStage_covers (n : ℕ) : ∀ t < n, t ∈ algorithmStage n := by
  induction n with
  | zero =>
    intro t ht
    omega
  | succ n ih =>
    intro t ht
    by_cases heq : t = n
    · subst t
      exact (extendAlgorithm_spec _ _ (algorithmStage_safe n)).2.2 n (by simp)
    · exact (algorithmStage_prefix n).sublist.subset (ih t (by omega))

/-- The particular computable permutation of `ℕ₀` specified by the singleton
targets in the final remark. Both this map and its inverse are executable. -/
def explicitPermutation : ℕ ≃ ℕ :=
  permutationOfSafeStages bits algorithmStage algorithmStage_safe
    algorithmStage_prefix algorithmStage_covers

/-- The permutation computed in the final remark is 4AP-free. This connects
the executable algorithm to the theorem, rather than merely checking examples. -/
theorem explicitPermutation_apFree : SequenceAPFree explicitPermutation :=
  permutationOfSafeStages_apFree bits algorithmStage algorithmStage_safe
    algorithmStage_prefix algorithmStage_covers

/-- The stopping criterion in the final remark: any stage long enough to
contain a position already gives the final value at that position. -/
theorem explicitPermutation_eq_getElem (n i : ℕ)
    (hi : i < (algorithmStage n).length) :
    explicitPermutation i = (algorithmStage n)[i] :=
  permutationOfSafeStages_eq_getElem bits algorithmStage algorithmStage_safe
    algorithmStage_prefix algorithmStage_covers n i hi

/-- Reading a finite initial segment from a sufficiently long stage agrees
with the actual infinite permutation. This is the list form of the stopping
criterion and justifies the displayed numerical example in the remark. -/
theorem explicitPermutation_prefix (n m : ℕ) (hm : m ≤ (algorithmStage n).length) :
    (List.range m).map explicitPermutation = (algorithmStage n).take m := by
  apply List.ext_getElem
  · simp [List.length_take, hm]
  · intro i hi hj
    have hi' : i < m := by simpa using hi
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    exact explicitPermutation_eq_getElem n i (lt_of_lt_of_le hi' hm)

/-- Add one to the executable permutation, as in the last sentence of the
proof and the second displayed prefix in the final remark. Positions remain
zero-based here so the sequence can be read directly using Lean lists. -/
def explicitPositiveSequence : ℕ ≃ ℕ+ :=
  explicitPermutation.trans Equiv.pnatEquivNat.symm

/-- The positive sequence is the nonnegative permutation shifted by one,
exactly as stated in the paper. -/
@[simp] theorem explicitPositiveSequence_apply (i : ℕ) :
    (explicitPositiveSequence i : ℕ) = explicitPermutation i + 1 := rfl

/-- The explicit positive sequence avoids every nonconstant four-term AP,
including negative integer differences. This is the theorem's conclusion
for the particular computable construction in the final remark. -/
theorem explicitPositiveSequence_apFree : ∀ i j k l : ℕ,
    i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
    ¬ (((explicitPositiveSequence i : ℕ) : ℤ) = a ∧
       ((explicitPositiveSequence j : ℕ) : ℤ) = a + r ∧
       ((explicitPositiveSequence k : ℕ) : ℤ) = a + 2 * r ∧
       ((explicitPositiveSequence l : ℕ) : ℤ) = a + 3 * r) := by
  intro i j k l hij hjk hkl a r hr h
  simp only [explicitPositiveSequence_apply] at h
  apply explicitPermutation_apFree hij hjk hkl
  rcases h with ⟨ha, hb, hc, hd⟩
  unfold IsAP4
  constructor
  · intro hab
    have : (explicitPermutation i : ℤ) = explicitPermutation j :=
      congrArg (fun n : ℕ => (n : ℤ)) hab
    omega
  · constructor <;> omega

/-- The actual computable permutation of positive integers, with both values
and positions indexed by `ℕ+`, matching the paper's `a₁ a₂ …` convention. -/
def explicitPositivePermutation : ℕ+ ≃ ℕ+ :=
  Equiv.pnatEquivNat.trans explicitPositiveSequence

/-- The paper's main theorem for the explicitly constructed positive
permutation, now also with positive-integer positions. -/
theorem explicitPositivePermutation_apFree : ∀ i j k l : ℕ+,
    i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
    ¬ (((explicitPositivePermutation i : ℕ) : ℤ) = a ∧
       ((explicitPositivePermutation j : ℕ) : ℤ) = a + r ∧
       ((explicitPositivePermutation k : ℕ) : ℤ) = a + 2 * r ∧
       ((explicitPositivePermutation l : ℕ) : ℤ) = a + 3 * r) := by
  intro i j k l hij hjk hkl a r hr
  exact explicitPositiveSequence_apFree i.natPred j.natPred k.natPred l.natPred
    (PNat.natPred_strictMono hij) (PNat.natPred_strictMono hjk)
    (PNat.natPred_strictMono hkl) a r hr

end FourAP

-- ===== FourAP/Main.lean (Boon Suan Ho, MIT) =====
/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

/-!
# The theorem of the paper

The declarations here assemble the preceding modules into the unconditional
existence theorem of the paper “A 4AP-free permutation of the positive
integers”. For the closest match to the displayed theorem in the paper, see
`exists_fourAPFree_positive_permutation`, which uses positive integers both
as positions and as values, and an arbitrary nonzero integer difference.
Each existential statement below uses the explicit, verified construction.
-/
namespace FourAP

/-- The main theorem before the final shift: a permutation of `ℕ₀` with no
four-term arithmetic progression in increasing positions. -/
theorem exists_fourAPFree_permutation : ∃ f : ℕ ≃ ℕ, SequenceAPFree f :=
  ⟨explicitPermutation, explicitPermutation_apFree⟩

/-- The main theorem after adding one to every value, retaining zero-based
positions for compatibility with Lean lists and sequences. -/
theorem exists_fourAPFree_positive_sequence :
    ∃ f : ℕ ≃ ℕ+, ∀ i j k l : ℕ,
      i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
      ¬ (((f i : ℕ) : ℤ) = a ∧ ((f j : ℕ) : ℤ) = a + r ∧
         ((f k : ℕ) : ℤ) = a + 2 * r ∧ ((f l : ℕ) : ℤ) = a + 3 * r) :=
  ⟨explicitPositiveSequence, explicitPositiveSequence_apFree⟩

/-- **The theorem of the paper.** There exists a permutation of the positive
integers containing no subsequence `a, a+r, a+2r, a+3r` with `r ≠ 0` in `ℤ`.

A Lean equivalence supplies both injectivity and surjectivity: no value is
repeated or omitted. The indices here are positive integers, matching the
paper's convention `a₁ a₂ …`. Negative common differences are included. -/
theorem exists_fourAPFree_positive_permutation :
    ∃ f : ℕ+ ≃ ℕ+, ∀ i j k l : ℕ+,
      i < j → j < k → k < l → ∀ a r : ℤ, r ≠ 0 →
      ¬ (((f i : ℕ) : ℤ) = a ∧ ((f j : ℕ) : ℤ) = a + r ∧
         ((f k : ℕ) : ℤ) = a + 2 * r ∧ ((f l : ℕ) : ℤ) = a + 3 * r) :=
  ⟨explicitPositivePermutation, explicitPositivePermutation_apFree⟩

end FourAP

namespace Erdos195

/-- Ho's theorem (Erdős #196) in the mission's `HasMonotoneAP` language: a permutation of `ℕ`
with no monotone 4-term AP. Derived from `FourAP.exists_fourAPFree_permutation`
(B. S. Ho, github.com/boonsuan/4ap, MIT), included above. -/
theorem ho_nat_fourAP_free : ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP (fun n => (f n : ℤ)) 4 := by
  obtain ⟨f, hf⟩ := FourAP.exists_fourAPFree_permutation
  refine ⟨f, ?_⟩
  rintro ⟨l, ⟨a, d, hap⟩, hl⟩
  have hlen : l.length = 4 := by
    rcases hap with h | h <;> simpa using congrArg List.length h
  match l, hlen with
  | [i, j, k, m], _ =>
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hl
    obtain ⟨⟨hij, hik, him⟩, ⟨hjk, hjm⟩, hkm⟩ := hl
    have hne : f i ≠ f j := fun h => by
      have := f.injective h; omega
    rcases hap with h | h
    · simp [List.range_succ] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have e1 : ((f i : ℕ) : ℤ) + (f k : ℕ) = 2 * (f j : ℕ) := by omega
      have e2 : ((f j : ℕ) : ℤ) + (f m : ℕ) = 2 * (f k : ℕ) := by omega
      exact hf (i := i) (j := j) (k := k) (l := m) hij hjk hkm.1 ⟨hne, by exact_mod_cast e1, by exact_mod_cast e2⟩
    · simp [List.range_succ] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have e1 : ((f i : ℕ) : ℤ) + (f k : ℕ) = 2 * (f j : ℕ) := by omega
      have e2 : ((f j : ℕ) : ℤ) + (f m : ℕ) = 2 * (f k : ℕ) := by omega
      exact hf (i := i) (j := j) (k := k) (l := m) hij hjk hkm.1 ⟨hne, by exact_mod_cast e1, by exact_mod_cast e2⟩

end Erdos195



open Erdos195 in
theorem solution : ∃ f : ℕ ≃ ℕ, ¬ HasMonotoneAP (fun n => (f n : ℤ)) 4 :=
  Erdos195.ho_nat_fourAP_free
