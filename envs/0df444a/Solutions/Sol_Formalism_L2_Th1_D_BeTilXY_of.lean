-- Prove2me | solution 1 for Formalism.L2.Th1.D.BeTilXY_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:55.786875+00:00
-- url     : https://prove2.me/submissions/2b6ebed9-fcb0-49be-89a6-7d8185d2ea3a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_cc_zXY
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_comb_zXY
import Theorems.Thm_P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linE__d777e292ff70
import Theorems.Thm_P2M_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_subst_linO__ed8c3b4cc9e5
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_L2_Th1_D_Pair_addC_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_linE
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_linO
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst2_comp
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq UnrOK IsLawOfLog frobVar frobVar_eq_expand)
open MvPowerSeries
open Pair TranslateJetMomentLawAnyIdempotentLevel
namespace Formalism.L2.Th1.D
theorem _root_.solution (hE : ExpSpec) : BeTilXY := by
  intro K _ _ l d _ σ hl hd be0 ι _ _ om oms hfix hT
  have hz : HasSubst (zXY (d := d) l σ om oms) :=
    hasSubst_of_constantCoeff_zero (cc_zXY hl σ om oms)
  unfold beTil beXY
  rw [subst_sum hz]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [subst2_comp hz (cc_linE σ _) (cc_linO σ _), subst_linE' σ om oms r hz,
    subst_linO' σ om oms r hz, comb_zXY hd l σ hfix hT, comb_zXY hd l σ hfix hT]
  exact addC_log hE hl (by simp) (by simp) be0
end Formalism.L2.Th1.D
