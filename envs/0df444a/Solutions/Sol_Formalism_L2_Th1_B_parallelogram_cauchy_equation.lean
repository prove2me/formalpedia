-- Prove2me | solution 1 for Formalism.L2.Th1.B.parallelogram_cauchy_equation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:32:00.407727+00:00
-- url     : https://prove2.me/submissions/659b8883-d7f8-466a-8de5-00b4b0488161

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_evalYZero_add
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_sub
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_at_sum
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_at_difference
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_at_variable_zero
import Theorems.Thm_Formalism_L2_Th1_B_restrictSecondZero_inVar_one
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_one_parallelogram_defect
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series


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
open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)
namespace Formalism.L2.Th1.B
theorem _root_.solution : ParCauchy := by
  intro K _ _ f hf0 hf1
  have hd0 : PowerSeries.constantCoeff (dz f) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add, hf1,
      zero_mul]
  constructor
  · simp only [par0, two_mul]
    rw [eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, evalYZero_add, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, hf0,
      map_zero]
    abel
  · rw [pderiv_one_parallelogram_defect]
    simp only [two_mul]
    rw [eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, restrictSecondZero_inVar_one, hd0, map_zero]
    abel
end Formalism.L2.Th1.B
