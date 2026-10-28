-- Prove2me | solution 1 for D1Bound5.reciprocal_anchor_weight_standard
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:35:00.394991+00:00
-- url     : https://prove2.me/submissions/4e1f188c-16f1-4dec-870c-e8895a81e37d

import Mathlib.LinearAlgebra.Lagrange
import Theorems.Thm_D1Bound5_reciprocal_anchor_weight_term
import Theorems.Thm_D1Bound5_reciprocal_vandermonde_reverse

section
open Polynomial Finset

namespace D1Bound5







/-- The reciprocal-node transfer with the standard Lagrange orientation.
This is the precise all-order weight reduction used for negative powers
of the original interpolation anchors. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (i : ι) (hi : i ∈ s) (k : ℕ) :
    ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j)) =
      (-1 : F) ^ (s.card - 1) * (∏ j ∈ s, a j)⁻¹ *
        ((a i)⁻¹) ^ (k + s.card - 1) /
        (∏ j ∈ s.erase i, ((a i)⁻¹ - (a j)⁻¹)) := by
  rw [reciprocal_anchor_weight_term s a ha i hi k,
    Finset.card_erase_of_mem hi,
    reciprocal_vandermonde_reverse s a i hi]
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hexp : k + s.card - 1 = k + (s.card - 1) := by omega
  have hsign : ((-1 : F) ^ (s.card - 1))⁻¹ = (-1 : F) ^ (s.card - 1) := by
    rw [← inv_pow]
    simp
  simp [div_eq_mul_inv, mul_inv_rev, mul_assoc, pow_add, hexp, hsign]
  ring





end D1Bound5
end
