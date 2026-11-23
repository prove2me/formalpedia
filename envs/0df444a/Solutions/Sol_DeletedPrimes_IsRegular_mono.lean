-- Prove2me | solution 1 for DeletedPrimes.IsRegular.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:47:50.000662+00:00
-- url     : https://prove2.me/submissions/8cc13cd8-7d9e-4b3c-bcf8-46a9733f30a4

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_IsRegular_nonneg_const

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
namespace IsRegular
theorem _root_.solution {S : Set ℕ} {θ θ' : ℝ} (h : IsRegular S θ) (hθ : θ ≤ θ') : IsRegular S θ' := by
  obtain ⟨C, hC⟩ := h
  have hC0 := IsRegular.nonneg_const hC
  refine ⟨C, fun x hx => le_trans (hC x hx) ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hθ) hC0
end IsRegular
end DeletedPrimes
