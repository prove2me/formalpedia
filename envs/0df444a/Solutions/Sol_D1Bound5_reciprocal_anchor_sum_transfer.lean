-- Prove2me | solution 1 for D1Bound5.reciprocal_anchor_sum_transfer
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T01:34:16.592581+00:00
-- url     : https://prove2.me/submissions/aefc7274-7a39-46a4-a6e2-06e5baf902d2

import Mathlib.LinearAlgebra.Lagrange
import Theorems.Thm_D1Bound5_reciprocal_anchor_weight_standard

section
open Polynomial Finset

namespace D1Bound5









/-- For every order, a negative-power barycentric sum at nonzero
anchors transfers to an ordinary positive-power Lagrange moment of their
reciprocals. The sign and total product are exact. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (k : ℕ) :
    (∑ i ∈ s, ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      ((-1 : F) ^ (s.card - 1) * (∏ j ∈ s, a j)⁻¹) *
        (∑ i ∈ s, ((a i)⁻¹) ^ (k + s.card - 1) /
          (∏ j ∈ s.erase i, ((a i)⁻¹ - (a j)⁻¹))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [div_eq_mul_inv, mul_assoc] using
    reciprocal_anchor_weight_standard s a ha i hi k



end D1Bound5
end
