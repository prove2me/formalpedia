-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.sum_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:29:09.594517+00:00
-- url     : https://prove2.me/submissions/c901ce6e-ec27-4394-a8df-8161bad4c79d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_parity_sub_one
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_iter_sub_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution (hd : Even d) (σ : K →+* K) {c : K} (hc : σ^[d] c = c) :
    (∑ s : ZMod d, if s.val % 2 = 0 then 0 else σ^[s.val] c) =
      σ (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] c else 0) := by
  rw [map_sum]
  refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod d)) _ _ ?_
  intro s
  simp only [Equiv.subRight_apply]
  have hp := parity_sub_one hd s
  have hi := iter_sub_one (⇑σ) hc s
  by_cases h : s.val % 2 = 0
  · have h' : ¬ (s - 1).val % 2 = 0 := fun h'' => (hp.1 h'') h
    rw [if_pos h, if_neg h', map_zero]
  · rw [if_neg h, if_pos (hp.2 h)]
    exact hi.symm
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
