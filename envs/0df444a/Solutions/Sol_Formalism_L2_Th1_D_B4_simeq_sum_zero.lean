-- Prove2me | solution 1 for Formalism.L2.Th1.D.B4.simeq_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:22.911544+00:00
-- url     : https://prove2.me/submissions/6021ba28-78b3-453c-bd42-2484ab722a26

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Theorems.Thm_Formalism_L2_Th1_D_B4_simeq_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_sum


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
open Formalism.L2.Th1.D.B4
variable {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.D.B4
theorem _root_.solution {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K)
    (h : ∀ a ∈ s, Simeq (f a) 0) : Simeq (∑ a ∈ s, f a) 0 := by
  simpa using simeq_sum s f (fun _ => 0) h
end Formalism.L2.Th1.D.B4
