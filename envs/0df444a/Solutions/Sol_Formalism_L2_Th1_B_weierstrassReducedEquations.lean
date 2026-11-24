-- Prove2me | solution 1 for Formalism.L2.Th1.B.weierstrassReducedEquations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:02.174158+00:00
-- url     : https://prove2.me/submissions/63bce63d-e7fc-452a-a866-94e62dc4f286

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_WeierstrassReducedEquations
import Theorems.Thm_Formalism_L2_Th1_B_dz_ofNat
import Theorems.Thm_Formalism_L2_Th1_B_dz_one
import Theorems.Thm_Formalism_L2_Th1_B_dz_C
import Theorems.Thm_Formalism_L2_Th1_B_dz_X
import Theorems.Thm_Formalism_L2_Th1_B_dz_add
import Theorems.Thm_Formalism_L2_Th1_B_dz_sub
import Theorems.Thm_Formalism_L2_Th1_B_dz_mul
import Theorems.Thm_Formalism_L2_Th1_B_dz_two
import Theorems.Thm_Formalism_L2_Th1_B_dz_four
import Theorems.Thm_Formalism_L2_Th1_B_two_ne
import Theorems.Thm_Formalism_L2_Th1_B_dz_sq
import Theorems.Thm_Formalism_L2_Th1_B_dz_cube
import Theorems.Thm_Formalism_L2_Th1_B_X_ne
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
theorem _root_.solution : WpReduced := by
  intro K _ _ g2 g3 P hP
  obtain ⟨_, _, hE⟩ := hP
  have E1 : X ^ 4 * dz P ^ 2 - 4 * X * dz P =
      12 * P + 12 * X ^ 2 * P ^ 2 + 4 * X ^ 4 * P ^ 3 - C g2 * X ^ 2 * (1 + X ^ 2 * P) -
        C g3 * X ^ 4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (X_ne (K := K)))
    linear_combination hE
  refine ⟨E1, ?_⟩
  have hg : (C g2 : PowerSeries K) = 2 * C (g2 / 2) := by
    rw [← map_ofNat C 2, ← map_mul]
    congr 1
    field_simp
  rw [hg] at E1
  have d4 : dz ((X : PowerSeries K) ^ 4) = 4 * X ^ 3 := by
    rw [show (X : PowerSeries K) ^ 4 = (X ^ 2) ^ 2 by ring, dz_sq, dz_sq, dz_X]
    ring
  have hdiff : 4 * X ^ 3 * dz P ^ 2 + 2 * X ^ 4 * dz P * dz (dz P) - 4 * dz P - 4 * X * dz (dz P) =
      12 * dz P + 24 * X * P ^ 2 + 24 * X ^ 2 * P * dz P + 16 * X ^ 3 * P ^ 3 +
        12 * X ^ 4 * P ^ 2 * dz P - 2 * C (g2 / 2) * (2 * X + 4 * X ^ 3 * P + X ^ 4 * dz P) -
        4 * C g3 * X ^ 3 := by
    have h := congrArg dz E1
    have c12 : dz (12 : PowerSeries K) = 0 := dz_ofNat 12
    simp only [dz_add, dz_sub, dz_mul, dz_sq, dz_cube, dz_C, dz_X, dz_two, dz_four, c12, dz_one, d4] at h
    linear_combination h
  refine mul_left_cancel₀ (?_ : (2 * X * (X ^ 3 * dz P - 2) : PowerSeries K) ≠ 0) ?_
  · refine mul_ne_zero (mul_ne_zero two_ne X_ne) (ne_zero_of_constantCoeff ?_)
    rw [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, map_ofNat]
    norm_num
  · linear_combination X ^ 2 * hdiff - 4 * X * E1
end Formalism.L2.Th1.B
