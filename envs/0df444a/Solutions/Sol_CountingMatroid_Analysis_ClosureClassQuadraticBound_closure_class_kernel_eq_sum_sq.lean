-- Prove2me | solution 1 for CountingMatroid.Analysis.ClosureClassQuadraticBound.closure_class_kernel_eq_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:44:11.012831+00:00
-- url     : https://prove2.me/submissions/500558f7-2768-4793-87ac-330b3d2d79c2

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
set_option autoImplicit false

/-! The quadratic correction indexed by equal closure classes is nonnegative:
it is a sum of squares of the sums within each class. -/

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
end CountingMatroid.Analysis.ClosureClassQuadraticBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ClosureClassQuadraticBound
open scoped BigOperators

/-- INTERNAL: An equality kernel is the sum of the squares of its fiber sums.
TEXLINE: main.tex:334-348 -/
theorem solution {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (u : α → ℝ) :
    (∑ a ∈ T, ∑ b ∈ T, if f a = f b then u a * u b else 0) =
      ∑ j ∈ T.image f, (∑ a ∈ T with f a = j, u a) ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image f) (g := f)
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (fun a => ∑ b ∈ T, if f a = f b then u a * u b else 0)]
  apply Finset.sum_congr rfl
  intro j hj
  have hinner (a : α) (ha : a ∈ T.filter (fun a => f a = j)) :
      (∑ b ∈ T, if f a = f b then u a * u b else 0) =
        u a * ∑ b ∈ T with f b = j, u b := by
    have ha' := (Finset.mem_filter.mp ha).2
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [ha', eq_comm (a := j), mul_ite, mul_zero]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  ring
