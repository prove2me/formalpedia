-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_N_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:54.505155+00:00
-- url     : https://prove2.me/submissions/9a88a68f-72dd-464f-aac0-2c19768e1c66

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_ge_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (κ C₁ C₂ M T δ : ℝ) (hκ : 0 < κ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hM : 3 ≤ M) (hT : 2 ≤ T)
    (_hδ0 : 0 < δ) (hδ : κ / (C₁ * (T + 1) * Real.log (M * (T + 2))) ≤ δ) :
    C₂ * (2 * Real.log (M * T)) / δ ≤ 6 * C₁ * C₂ / κ * (T * Real.log (M * T) ^ 2) := by
  have hL : 1 ≤ Real.log (M * T) := exm_log_ge_one M T hM hT
  have hL' : Real.log (M * (T + 2)) ≤ 2 * Real.log (M * T) :=
    exm_log_le M T T hM hT (by linarith) (by linarith)
  have hL'1 : 1 ≤ Real.log (M * (T + 2)) := exm_log_ge_one M (T + 2) hM (by linarith)
  have hA : 0 < C₁ * (T + 1) * Real.log (M * (T + 2)) :=
    mul_pos (mul_pos hC₁ (by linarith)) (by linarith)
  have hinv : 1 / δ ≤ C₁ * (T + 1) * Real.log (M * (T + 2)) / κ := by
    have := one_div_le_one_div_of_le (div_pos hκ hA) hδ
    rwa [one_div_div] at this
  have hP : 0 ≤ C₁ * C₂ * Real.log (M * T) := mul_nonneg (mul_nonneg hC₁.le hC₂.le) (by linarith)
  have e1 : (T + 1) * Real.log (M * (T + 2)) ≤ (T + 1) * (2 * Real.log (M * T)) :=
    mul_le_mul_of_nonneg_left hL' (by linarith)
  have e2 : (T + 1) * (2 * Real.log (M * T)) ≤ 3 * T * Real.log (M * T) := by
    nlinarith [mul_le_mul_of_nonneg_right hT (by linarith : (0:ℝ) ≤ Real.log (M * T))]
  have hnum : 2 * (C₁ * C₂ * Real.log (M * T)) * ((T + 1) * Real.log (M * (T + 2))) ≤
      2 * (C₁ * C₂ * Real.log (M * T)) * (3 * T * Real.log (M * T)) :=
    mul_le_mul_of_nonneg_left (e1.trans e2) (by linarith)
  calc C₂ * (2 * Real.log (M * T)) / δ = C₂ * (2 * Real.log (M * T)) * (1 / δ) := by ring
    _ ≤ C₂ * (2 * Real.log (M * T)) * (C₁ * (T + 1) * Real.log (M * (T + 2)) / κ) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg hC₂.le (by linarith))
    _ = 2 * (C₁ * C₂ * Real.log (M * T)) * ((T + 1) * Real.log (M * (T + 2))) * κ⁻¹ := by ring
    _ ≤ 2 * (C₁ * C₂ * Real.log (M * T)) * (3 * T * Real.log (M * T)) * κ⁻¹ :=
        mul_le_mul_of_nonneg_right hnum (inv_nonneg.2 hκ.le)
    _ = 6 * C₁ * C₂ / κ * (T * Real.log (M * T) ^ 2) := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
