-- Prove2me | solution 1 for Formalism.L2.Th1.B.Jets.constantCoeff_subst_law_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:21:14.887557+00:00
-- url     : https://prove2.me/submissions/d97096a4-3b29-4b50-b046-387d1ac100dc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_OneAddMulDerivLogSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_EvalSecondZeroAtVariableZero
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_InvariantDerivationSubstLawThree
import Theorems.Thm_Formalism_L2_Th1_B_Jets_constantCoeff_law_three
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
variable {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K}
namespace Formalism.L2.Th1.B.Jets
theorem _root_.solution (hF : MvPowerSeries.constantCoeff F = 0) (g : PowerSeries K) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (U3 F) g) = PowerSeries.constantCoeff g := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_law_three hF)
  have hg : g = PowerSeries.C (PowerSeries.constantCoeff g) +
      (g - PowerSeries.C (PowerSeries.constantCoeff g)) := by ring
  have h0 : PowerSeries.constantCoeff (g - PowerSeries.C (PowerSeries.constantCoeff g)) = 0 := by
    simp
  conv_lhs => rw [hg]
  rw [PowerSeries.subst_add hs, PowerSeries.subst_C, map_add, MvPowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_law_three hF) _ h0, add_zero]
end Formalism.L2.Th1.B.Jets
