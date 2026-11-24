-- Prove2me | solution 1 for Formalism.L2.Th1.B.wave_operator_kills
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:40.260566+00:00
-- url     : https://prove2.me/submissions/9c1d6d57-8299-4f1d-82b7-f2ceee203962

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_pd_atS
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_zero_series_at_difference
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_one_series_at_difference
import Theorems.Thm_Formalism_L2_Th1_B_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_at_variable_of_ne
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_zero_parallelogram_defect
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
theorem _root_.solution : WaveKills := by
  intro K _ _ f
  rw [pderiv_zero_parallelogram_defect, pderiv_one_parallelogram_defect]
  simp only [two_mul, map_add, map_sub, map_neg, pd_atS, pderiv_zero_series_at_difference, pderiv_one_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne (show (1 : Fin 2) ≠ 0 by decide), pderiv_at_variable_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  ring
end Formalism.L2.Th1.B
