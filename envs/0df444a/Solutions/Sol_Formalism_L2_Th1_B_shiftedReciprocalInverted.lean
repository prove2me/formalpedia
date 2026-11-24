-- Prove2me | solution 1 for Formalism.L2.Th1.B.shiftedReciprocalInverted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:22:08.323294+00:00
-- url     : https://prove2.me/submissions/1daf9ba6-c3b9-4841-801d-92eb131e1752

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Theorems.Thm_Formalism_L2_Th1_B_dz_one
import Theorems.Thm_Formalism_L2_Th1_B_dz_C
import Theorems.Thm_Formalism_L2_Th1_B_dz_X
import Theorems.Thm_Formalism_L2_Th1_B_dz_add
import Theorems.Thm_Formalism_L2_Th1_B_dz_sub
import Theorems.Thm_Formalism_L2_Th1_B_dz_mul
import Theorems.Thm_Formalism_L2_Th1_B_dz_sq
import Theorems.Thm_Formalism_L2_Th1_B_ne_zero_of_constantCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open PowerSeries
namespace Formalism.L2.Th1.B
theorem _root_.solution : WOfWp := by
  intro K _ _ g2 g3 e1 P hP he
  obtain ⟨_, _, hE⟩ := hP
  have hu : constantCoeff (1 + X ^ 2 * P - C e1 * X ^ 2) ≠ 0 := by simp
  have hw : (1 + X ^ 2 * P - C e1 * X ^ 2) * wOf e1 P = X ^ 2 := by
    rw [wOf, mul_left_comm, PowerSeries.mul_inv_cancel _ hu, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · rw [wOf]
    simp
  · rw [wOf, PowerSeries.coeff_X_pow_mul']
    simp [PowerSeries.constantCoeff_inv]
  · have hdu : dz (1 + X ^ 2 * P - C e1 * X ^ 2) = 2 * X * P + X ^ 2 * dz P - 2 * C e1 * X := by
      simp only [dz_add, dz_sub, dz_mul, dz_one, dz_C, dz_X, dz_sq]
      ring
    have hd := congrArg dz hw
    rw [dz_mul, hdu, dz_sq, dz_X] at hd

    have hA : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) = -X * (X ^ 3 * dz P - 2) := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) * hd - (2 * X * P + X ^ 2 * dz P - 2 * C e1 * X) * hw
    have h1 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P = X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 := by
      linear_combination (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * hw
    have h2 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 2 = X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2) * hw
    have h3 : (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 4 * wOf e1 P ^ 3 = X ^ 6 * (1 + X ^ 2 * P - C e1 * X ^ 2) := by
      linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 3 * wOf e1 P ^ 2 + X ^ 2 * (1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * wOf e1 P + X ^ 4 * (1 + X ^ 2 * P - C e1 * X ^ 2)) * hw
    have hg4 : (C g2 : PowerSeries K) = 4 * C (g2 / 4) := by
      rw [← map_ofNat C 4, ← map_mul]
      congr 1
      field_simp
    rw [hg4] at hE
    have he' : 4 * C e1 ^ 3 - 4 * C (g2 / 4) * C e1 - C g3 = (0 : PowerSeries K) := by
      have hc := congrArg (C (R := K)) he
      rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_ofNat, map_zero, hg4] at hc
      linear_combination hc
    rw [show (C (3 * e1) : PowerSeries K) = 3 * C e1 by rw [map_mul, map_ofNat],
      show (C (3 * e1 ^ 2 - g2 / 4) : PowerSeries K) = 3 * C e1 ^ 2 - C (g2 / 4) by
        rw [map_sub, map_mul, map_pow, map_ofNat]]
    refine mul_left_cancel₀ (pow_ne_zero 4 (ne_zero_of_constantCoeff hu)) ?_
    linear_combination ((1 + X ^ 2 * P - C e1 * X ^ 2) ^ 2 * dz (wOf e1 P) - X * (X ^ 3 * dz P - 2)) * hA - 4 * h1 -
      12 * C e1 * h2 - 4 * (3 * C e1 ^ 2 - C (g2 / 4)) * h3 + X ^ 2 * hE + X ^ 8 * he'
end Formalism.L2.Th1.B
