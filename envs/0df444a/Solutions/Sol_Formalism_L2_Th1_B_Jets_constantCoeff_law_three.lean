-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.constantCoeff_law_three
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:44.606468+00:00
-- url     : https://prove2.me/submissions/37191b84-78b1-4d18-bd8f-a92f3f8bb2d6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_ccX
import Theorems.Thm_Formalism_L2_Th1_B_Jets_cc_law
import Theorems.Thm_Formalism_L2_Th1_B_Jets_constantCoeff_law_pair
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_injective
import Theorems.Thm_Formalism_G_LogP_psubst_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Jets
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3)
open Formalism.G.LogP (hs2 psubst_subst constantCoeff_subst_of_zero psubst_injective)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (U3 F) = 0 := by
  unfold U3
  exact cc_law hF (constantCoeff_law_pair hF 0 1) (ccX 2)
end Formalism.L2.Th1.B.Jets
