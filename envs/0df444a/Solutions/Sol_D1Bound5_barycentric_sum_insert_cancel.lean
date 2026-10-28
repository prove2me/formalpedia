-- Prove2me | solution 1 for D1Bound5.barycentric_sum_insert_cancel
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:08.637756+00:00
-- url     : https://prove2.me/submissions/00436baf-2098-4837-b117-24b5e47b3c6b

import Mathlib.LinearAlgebra.Lagrange
import Theorems.Thm_D1Bound5_barycentric_denominator_insert

section
open Polynomial Finset

namespace D1Bound5



/-- Multiplication of arbitrary nodal data by the new-node difference
removes that node from the barycentric sum. Old node values may coincide. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a g : ι → F) (t : ι)
    (ht : t ∉ s) (hsep : ∀ i ∈ s, a i ≠ a t) :
    (∑ i ∈ insert t s,
      ((a i - a t) * g i) /
        (∏ j ∈ (insert t s).erase i, (a i - a j))) =
      ∑ i ∈ s, g i / (∏ j ∈ s.erase i, (a i - a j)) := by
  rw [Finset.sum_insert ht]
  simp only [sub_self, zero_mul, zero_div, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [barycentric_denominator_insert s a t i ht hi]
  exact mul_div_mul_left (g i)
    (∏ j ∈ s.erase i, (a i - a j))
    (sub_ne_zero.mpr (hsep i hi))



end D1Bound5
end
