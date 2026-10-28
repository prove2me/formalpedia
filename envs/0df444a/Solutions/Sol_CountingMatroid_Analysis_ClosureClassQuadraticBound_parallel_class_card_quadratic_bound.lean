-- Prove2me | solution 1 for CountingMatroid.Analysis.ClosureClassQuadraticBound.parallel_class_card_quadratic_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:26:51.520089+00:00
-- url     : https://prove2.me/submissions/80580b58-7e16-4fcd-a73a-381453e26d78

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_ClosureClassQuadraticBound_closure_class_kernel_eq_sum_sq

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
section


set_option autoImplicit false

/-! The quadratic correction indexed by equal closure classes is nonnegative:
it is a sum of squares of the sums within each class. -/

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
open scoped BigOperators



/-- INTERNAL: An equality kernel is positive semidefinite on every finite set.
TEXLINE: main.tex:334-348 -/
theorem closure_class_kernel_nonneg {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (u : α → ℝ) :
    0 ≤ ∑ a ∈ T, ∑ b ∈ T, if f a = f b then u a * u b else 0 := by
  rw [closure_class_kernel_eq_sum_sq]
  exact Finset.sum_nonneg (fun j hj => sq_nonneg _)

/-- INTERNAL: Cauchy–Schwarz on the fiber sums bounds the equality kernel
using at most as many classes as there are labels.
TEXLINE: main.tex:334-348 -/
theorem closure_class_kernel_card_bound {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (y : α → ℝ) :
    (∑ a ∈ T, y a) ^ 2 ≤ (T.card : ℝ) *
      (∑ a ∈ T, ∑ b ∈ T, if f a = f b then y a * y b else 0) := by
  have hk := closure_class_kernel_nonneg T f y
  rw [closure_class_kernel_eq_sum_sq] at hk ⊢
  have hf : (∑ j ∈ T.image f, ∑ a ∈ T with f a = j, y a) = ∑ a ∈ T, y a :=
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) y
  rw [← hf]
  exact (sq_sum_le_card_mul_sum_sq (s := T.image f)
    (f := fun j => ∑ a ∈ T with f a = j, y a)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le)
        hk)





end CountingMatroid.Analysis.ClosureClassQuadraticBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · expressed the class kernel as a sum of fiber squares and combined label and class Cauchy–Schwarz bounds to prove the sharp cardinality estimate, including undiscounted loops.
-/


end
set_option autoImplicit false

/-! The quadratic correction indexed by equal closure classes is nonnegative:
it is a sum of squares of the sums within each class. -/

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ClosureClassQuadraticBound
open scoped BigOperators

/-- INTERNAL: The discounted pair form satisfies the sharp cardinality bound.
Combining Cauchy–Schwarz for labels and for classes supplies the homogenizer
hyperplane estimate.
TEXLINE: main.tex:334-348 -/
theorem solution {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (y : α → ℝ) :
    (T.card : ℝ) * (∑ a ∈ T, ∑ b ∈ T,
      (if a = b then 0 else if f a = f b then q else 1) * y a * y b)
        ≤ ((T.card : ℝ) - 1) * (∑ a ∈ T, y a) ^ 2 := by
  have hdiag := sq_sum_le_card_mul_sum_sq (s := T) (f := y)
  have hclass := closure_class_kernel_card_bound T f y
  have hid : (∑ a ∈ T, y a) ^ 2 -
      (∑ a ∈ T, ∑ b ∈ T,
        (if a = b then 0 else if f a = f b then q else 1) * y a * y b) =
      q * (∑ a ∈ T, y a ^ 2) +
        (1 - q) * (∑ a ∈ T, ∑ b ∈ T, if f a = f b then y a * y b else 0) := by
    rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have hsingle : (∑ b ∈ T, if a = b then q * (y a) ^ 2 else 0) = q * (y a) ^ 2 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b hb hba; simp [Ne.symm hba]
      · exact fun h => (h ha).elim
    rw [← hsingle, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a = b
    · subst b; simp; ring
    · by_cases hf : f a = f b
      · simp only [if_neg hab, if_pos hf, zero_add]
        ring
      · simp [hab, hf]
  have hqdiag := mul_nonneg hq (sub_nonneg.mpr hdiag)
  have hqclass := mul_nonneg (sub_nonneg.mpr hqone) (sub_nonneg.mpr hclass)
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ T.card by positivity) (sq_nonneg (∑ a ∈ T, y a))]
