-- Prove2me | solution 1 for Formalism.L2.Th1.B.eval_second_zero_at_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:21:17.727553+00:00
-- url     : https://prove2.me/submissions/c9407a55-43d8-440e-a628-1fd090853ad1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_evalYZero_add
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_X_zero
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_X_one
import Theorems.Thm_Formalism_L2_Th1_B_evalYZero_subst
import Theorems.Thm_Formalism_L2_Th1_B_psubst_X
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
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B
theorem _root_.solution (f : PowerSeries K) : ev0 (atS f) = f := by
  unfold atS
  rw [evalYZero_subst _ (by simp), evalYZero_add, eval_second_zero_X_zero, eval_second_zero_X_one, add_zero, psubst_X]
end Formalism.L2.Th1.B
