-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.mXY_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:27.607351+00:00
-- url     : https://prove2.me/submissions/0c74859e-2c45-49f2-b6d3-a76fadb99e93

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_iter_sub_one
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_parity_sub_two_mul
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand
import Theorems.Thm_Formalism_LT_InvIntP_key


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
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K] {d : ℕ} [NeZero d] {ι : Type}
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution (hd : Even d) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (s : ZMod d) (x : Bool × ι) :
    σ (σ (mXY σ om oms (s - 2) x)) = mXY σ om oms s x := by
  have h2 : s - 2 = s - 1 - 1 := by ring
  have hp : (s - 2).val % 2 = s.val % 2 := by
    have := parity_sub_two_mul hd s 1
    simpa using this
  have key : ∀ c : K, σ^[d] c = c → σ (σ (σ^[(s - 2).val] c)) = σ^[s.val] c := by
    intro c hc
    rw [h2, iter_sub_one (⇑σ) hc (s - 1), iter_sub_one (⇑σ) hc s]
  obtain ⟨b, r⟩ := x
  unfold mXY
  by_cases h : s.val % 2 = 0
  · have h' : (s - 2).val % 2 = 0 := by omega
    cases b <;> simp [h, h', key _ (hfix r).1, key _ (hfix r).2]
  · have h' : ¬ (s - 2).val % 2 = 0 := by omega
    cases b <;> simp [h, h', key _ (hfix r).1, key _ (hfix r).2]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
