-- Prove2me | solution 1 for D1Bound5.reciprocal_vandermonde_product
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:27.631984+00:00
-- url     : https://prove2.me/submissions/f22d48bc-e801-43d7-a813-cd196a65e9ae

import Mathlib.LinearAlgebra.Lagrange

section
open Polynomial Finset

namespace D1Bound5

/-- A product of ordinary Vandermonde differences changes to reciprocal
nodes by an exact product identity. No distinctness is required. -/
theorem _root_.solution
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F)
    (ha : ∀ j ∈ s, a j ≠ 0) (i : ι) (hi : i ∈ s) :
    (∏ j ∈ s.erase i, (a i - a j)) =
      (a i) ^ (s.erase i).card *
        (∏ j ∈ s.erase i, a j) *
        (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) := by
  have hai : a i ≠ 0 := ha i hi
  calc
    (∏ j ∈ s.erase i, (a i - a j)) =
      ∏ j ∈ s.erase i, (a i * a j * ((a j)⁻¹ - (a i)⁻¹)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have hj0 : a j ≠ 0 := ha j (Finset.mem_of_mem_erase hj)
        field_simp [hai, hj0]
    _ = (a i) ^ (s.erase i).card *
        (∏ j ∈ s.erase i, a j) *
        (∏ j ∈ s.erase i, ((a j)⁻¹ - (a i)⁻¹)) := by
        simp_rw [mul_assoc, Finset.prod_mul_distrib, Finset.prod_const]











end D1Bound5
end
