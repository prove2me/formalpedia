-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.constantCoeff_defectTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:27.56974+00:00
-- url     : https://prove2.me/submissions/4becb836-d4ea-43a8-8aff-77df0d4902bb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substZero
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne__6454fc9e7ded
import Theorems.Thm_P2M_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo__588f1fb17580


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp NoLowBidegree letterLog de1 de2 s0 s1 s2 s1' s2' V2 degE)
open Formalism.InvariantFactorPaths.G7 (Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open B4
open Formalism.L2.Th1.D.B4
variable {K : Type} [Field K] {τ τ' : Type}
variable {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.B4
theorem _root_.solution {be : MvPowerSeries (ZMod d) K} (h : constantCoeff be = 0) :
    constantCoeff (de2 be) = 0 := by
  unfold de2
  rw [map_sub, map_sub,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne')
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne' h,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero)
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero h,
    MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo')
      Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo' h]
  simp
end Formalism.L2.Th1.D.B4
