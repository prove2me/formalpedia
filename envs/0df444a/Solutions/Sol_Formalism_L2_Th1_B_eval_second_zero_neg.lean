-- Prove2me | solution 1 for Formalism.L2.Th1.B.eval_second_zero_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:14:18.599672+00:00
-- url     : https://prove2.me/submissions/f0001589-6594-42f2-8ac5-ec3f3128e38d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_eval_second_zero_eq_algHom
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
theorem _root_.solution (h : MvPowerSeries (Fin 2) K) : ev0 (-h) = -ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_neg]
end Formalism.L2.Th1.B
