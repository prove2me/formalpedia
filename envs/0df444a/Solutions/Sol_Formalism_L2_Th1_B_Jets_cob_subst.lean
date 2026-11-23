-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.cob_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:31:04.403621+00:00
-- url     : https://prove2.me/submissions/e0952af0-6bb8-49ef-a536-582cfccd49e9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
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
theorem _root_.solution {ι : Type} {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) (f : PowerSeries K) {A B : MvPowerSeries ι K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hB : MvPowerSeries.constantCoeff B = 0) :
    MvPowerSeries.subst ![A, B] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![A, B] F) f - PowerSeries.subst A f -
        PowerSeries.subst B f := by
  have hAB : MvPowerSeries.HasSubst ![A, B] := hs2 hA hB
  simp only [cob, at1]
  rw [MvPowerSeries.subst_sub hAB, MvPowerSeries.subst_sub hAB, psubst_subst f hF hAB,
    psubst_subst f (MvPowerSeries.constantCoeff_X 0) hAB,
    psubst_subst f (MvPowerSeries.constantCoeff_X 1) hAB,
    MvPowerSeries.subst_X hAB, MvPowerSeries.subst_X hAB]
  simp
end Formalism.L2.Th1.B.Jets
