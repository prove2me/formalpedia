-- Prove2me | solution 1 for DeletedPrimes.IsMSRegular.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:01:34.1628+00:00
-- url     : https://prove2.me/submissions/715ede32-b1fb-4de7-81c4-c3eb814b7d57

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_IsRegular_nonneg_const
import Theorems.Thm_DeletedPrimes_IsMSRegular_nonneg_const

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
namespace IsMSRegular
theorem _root_.solution {S : Set ℕ} {θ θ' : ℝ} (h : IsMSRegular S θ) (hθ : θ ≤ θ') :
    IsMSRegular S θ' := by
  obtain ⟨C, hC⟩ := h
  have hC0 := IsMSRegular.nonneg_const hC
  refine ⟨C, fun X hX => le_trans (hC X hX) ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) hC0
end IsMSRegular
end DeletedPrimes
