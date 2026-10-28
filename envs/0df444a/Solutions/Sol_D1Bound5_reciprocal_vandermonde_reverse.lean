-- Prove2me | solution 1 for D1Bound5.reciprocal_vandermonde_reverse
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:41.929757+00:00
-- url     : https://prove2.me/submissions/0d772548-757e-46f4-85be-a4a46319641b

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5





/-- Reversing all reciprocal Vandermonde differences gives exactly the
parity sign for a full set of anchors. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (i : ι) (hi : i ∈ s) :
    (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) =
      (-1 : F) ^ (s.card - 1) *
        (∏ j ∈ s.erase i, ((a i)⁻¹ - (a j)⁻¹)) := by
  calc
    (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) =
      ∏ j ∈ s.erase i, -((a i)⁻¹ - (a j)⁻¹) := by
        apply Finset.prod_congr rfl
        intro j hj
        ring
    _ = _ := by
      rw [Finset.prod_neg, Finset.card_erase_of_mem hi]







end D1Bound5
end
