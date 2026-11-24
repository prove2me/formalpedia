-- Prove2me | solution 1 for Formalism.L2.Th1.B.SAdd.sigma_rules_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:39:08.907779+00:00
-- url     : https://prove2.me/submissions/ec52355c-f498-49c8-8b23-34e297aff681

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementE
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffQuotientXSq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_sW_sq
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_constantCoeff_sW
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_coeff_one_sW
import Theorems.Thm_Formalism_L2_Th1_B_SAdd_constantCoeff_dz_sW
import Theorems.Thm_Formalism_L2_Th1_B_dz_C
import Theorems.Thm_Formalism_L2_Th1_B_dz_add
import Theorems.Thm_Formalism_L2_Th1_B_dz_mul
import Theorems.Thm_Formalism_L2_Th1_B_dz_one
import Theorems.Thm_Formalism_L2_Th1_B_dz_sq
import Theorems.Thm_Formalism_L2_Th1_B_two_ne
import Theorems.Thm_Formalism_L2_Th1_B_wSecond


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.SAdd
open Formalism.InvariantFactorPaths.G7 (at1)
namespace Formalism.L2.Th1.B.SAdd
theorem _root_.solution : SRules := by
  intro K _ _ A kap w hw
  obtain ⟨hw1, -⟩ := wSecond K A kap w hw
  obtain ⟨hw0, hw2, hwE⟩ := hw
  have hsq := sW_sq hw0 hw1 hw2
  have hd : 2 * sW w * dz (sW w) = dz w := by
    rw [← dz_sq, hsq]
  have hwne : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hw2
    exact zero_ne_one hw2
  have h4 : (4 : PowerSeries K) ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact absurd this (by norm_num)
  have hs1 : dz (sW w) ^ 2 = 1 + PowerSeries.C A * w + PowerSeries.C kap * w ^ 2 := by
    refine mul_left_cancel₀ (mul_ne_zero h4 hwne) ?_
    linear_combination (-4 * dz (sW w) ^ 2) * hsq + (2 * sW w * dz (sW w) + dz w) * hd + hwE
  have hds : dz (sW w) ≠ 0 := by
    intro h
    have := constantCoeff_dz_sW hw2
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨hsq, constantCoeff_sW w, coeff_one_sW hw2, hd, hs1, ?_⟩
  have h5 := congrArg dz hs1
  rw [dz_sq, dz_add, dz_add, dz_one, dz_mul, dz_mul, dz_C, dz_C, dz_sq] at h5
  refine mul_left_cancel₀ (mul_ne_zero two_ne hds) ?_
  linear_combination h5 - (PowerSeries.C A + 2 * PowerSeries.C kap * w) * hd
end Formalism.L2.Th1.B.SAdd
