-- Prove2me | solution 1 for Formalism.L2.Th1.B.pderiv_zero_parallelogram_defect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:22:07.243652+00:00
-- url     : https://prove2.me/submissions/d4f413f0-0a43-4a11-8a5f-2e98617a315b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Theorems.Thm_Formalism_L2_Th1_B_pd_atS
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_zero_series_at_difference
import Theorems.Thm_Formalism_L2_Th1_B_partialDeriv_inVar_self
import Theorems.Thm_Formalism_L2_Th1_B_pderiv_at_variable_of_ne
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
theorem _root_.solution (f : PowerSeries K) :
    pd 0 (par0 f) = atS (dz f) + atD (dz f) - 2 * at1 0 (dz f) := by
  simp only [par0, two_mul, map_add, map_sub, pd_atS, pderiv_zero_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  abel
end Formalism.L2.Th1.B
