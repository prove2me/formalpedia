-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.first_difference_C_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:44:11.731932+00:00
-- url     : https://prove2.me/submissions/b8949aff-4370-4bb9-ae7b-1740b92c9ec1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_L2_Th1_D_B4_subst_C_mul_sum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substOne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substTwo
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_Transfer_constantCoeff_substZero


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
theorem _root_.solution (c : K) {α : Type} (s : Finset α) (f : α → MvPowerSeries (ZMod d) K) :
    de1 (MvPowerSeries.C c * ∑ k ∈ s, f k) = MvPowerSeries.C c * ∑ k ∈ s, de1 (f k) := by
  unfold de1
  rw [subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substOne),
    subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substZero),
    subst_C_mul_sum (MvPowerSeries.hasSubst_of_constantCoeff_zero Formalism.DworkPowerSeriesWeights.Transfer.constantCoeff_substTwo),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, mul_sub, mul_sub]
end Formalism.L2.Th1.D.B4
