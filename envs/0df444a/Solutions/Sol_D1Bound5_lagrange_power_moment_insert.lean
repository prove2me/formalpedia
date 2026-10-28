-- Prove2me | solution 1 for D1Bound5.lagrange_power_moment_insert
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:04.660291+00:00
-- url     : https://prove2.me/submissions/4d97ddd4-2f06-4c81-99da-a9c325199952

import Mathlib.LinearAlgebra.Lagrange
import Theorems.Thm_D1Bound5_barycentric_sum_insert_cancel

section
open Polynomial Finset

namespace D1Bound5





/-- The node-adjunction recurrence for every Lagrange power moment.
The only separation hypothesis concerns the newly added node. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (t : ι)
    (ht : t ∉ s) (hsep : ∀ i ∈ s, a i ≠ a t)
    (n : ℕ) :
    (∑ i ∈ insert t s,
      (a i) ^ (n + 1) / (∏ j ∈ (insert t s).erase i, (a i - a j))) =
      a t * (∑ i ∈ insert t s,
        (a i) ^ n / (∏ j ∈ (insert t s).erase i, (a i - a j))) +
      (∑ i ∈ s,
        (a i) ^ n / (∏ j ∈ s.erase i, (a i - a j))) := by
  calc
    _ = ∑ i ∈ insert t s,
        (a t * ((a i)^n / (∏ j ∈ (insert t s).erase i, (a i - a j))) +
        ((a i - a t) * (a i)^n) /
          (∏ j ∈ (insert t s).erase i, (a i - a j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    _ = a t * (∑ i ∈ insert t s,
        (a i)^n / (∏ j ∈ (insert t s).erase i, (a i - a j))) +
        (∑ i ∈ insert t s,
          ((a i - a t) * (a i)^n) /
            (∏ j ∈ (insert t s).erase i, (a i - a j))) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [barycentric_sum_insert_cancel s a (fun i => (a i)^n) t ht hsep]

end D1Bound5
end
