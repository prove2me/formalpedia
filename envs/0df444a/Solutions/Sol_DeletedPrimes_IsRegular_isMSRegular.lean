-- Prove2me | solution 1 for DeletedPrimes.IsRegular.isMSRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:05:36.582505+00:00
-- url     : https://prove2.me/submissions/30a28a1b-03b8-4291-8d72-2a99be9dec44

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_IsRegular_nonneg_const
import Theorems.Thm_DeletedPrimes_meanSq_le_of_pointwise
import Theorems.Thm_DeletedPrimes_IsMSRegular_nonneg_const

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
namespace IsRegular
theorem _root_.solution {S : Set ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (h : IsRegular S θ) :
    IsMSRegular S θ := by
  obtain ⟨C, hC⟩ := h
  have hC0 := IsRegular.nonneg_const hC
  refine ⟨(C * 2 ^ θ) ^ 2, fun X hX => meanSq_le_of_pointwise hX fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans hX hx.1
  have hx0 : 0 ≤ x := by linarith
  have hX0 : 0 ≤ X := by linarith
  have h1 : |err S x| ≤ C * x ^ θ := hC x hx1
  have h2 : C * x ^ θ ≤ C * (2 * X) ^ θ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hx.2 hθ) hC0
  have h3 : err S x ^ 2 ≤ (C * (2 * X) ^ θ) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (le_trans h1 h2) 2
  have h4 : X ^ (2 * θ) = (X ^ θ) ^ 2 := by
    rw [mul_comm, Real.rpow_mul hX0, Real.rpow_two]
  calc err S x ^ 2 ≤ (C * (2 * X) ^ θ) ^ 2 := h3
    _ = (C * 2 ^ θ) ^ 2 * X ^ (2 * θ) := by
      rw [h4, Real.mul_rpow (by norm_num) hX0]; ring
end IsRegular
end DeletedPrimes
