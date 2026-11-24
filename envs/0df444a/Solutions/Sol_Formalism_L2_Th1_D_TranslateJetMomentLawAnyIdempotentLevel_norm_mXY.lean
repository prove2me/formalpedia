-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.norm_mXY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:59:07.227974+00:00
-- url     : https://prove2.me/submissions/a84c76e5-18cd-4996-b55b-1598603a2f15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
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
open Pair TranslateJetMomentLawAnyIdempotentLevel
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [NormedField K] {d : ℕ} [NeZero d] {ι : Type}
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution {σ : K →+* K} (hσ : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1) {om oms : ι → K}
    (hn : ∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1) (s : ZMod d) (x : Bool × ι) :
    ‖mXY σ om oms s x‖ ≤ 1 := by
  have hit : ∀ (n : ℕ) (a : K), ‖a‖ ≤ 1 → ‖σ^[n] a‖ ≤ 1 := by
    intro n
    induction n with
    | zero => intro a ha; simpa using ha
    | succ n ih =>
      intro a ha
      rw [Function.iterate_succ_apply']
      exact hσ _ (ih a ha)
  unfold mXY
  split_ifs <;> first | exact hit _ _ (hn _).1 | exact hit _ _ (hn _).2 | simp
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
