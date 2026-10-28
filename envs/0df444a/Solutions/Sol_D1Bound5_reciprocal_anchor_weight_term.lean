-- Prove2me | solution 1 for D1Bound5.reciprocal_anchor_weight_term
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:36:08.497298+00:00
-- url     : https://prove2.me/submissions/7fed3f1a-6591-4ba4-a540-47ee07c54bfd

import Mathlib.LinearAlgebra.Lagrange
import Theorems.Thm_D1Bound5_reciprocal_vandermonde_product

section
open Polynomial Finset

namespace D1Bound5



/-- Pointwise transfer of barycentric weights from nodes `a` to
reciprocal nodes `a⁻¹`, valid even if some nodes coincide. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (i : ι) (hi : i ∈ s) (k : ℕ) :
    ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j)) =
      (∏ j ∈ s, a j)⁻¹ *
        ((a i)⁻¹) ^ (k + (s.erase i).card) /
        (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) := by
  rw [← Finset.mul_prod_erase s a hi,
    reciprocal_vandermonde_product s a ha i hi]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, pow_add, pow_one]
  ring









end D1Bound5
end
