-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.sumE_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:53.462802+00:00
-- url     : https://prove2.me/submissions/2bba2faa-c9c2-4900-8dd0-3ab4de94f11f

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
open Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
open Pair KernelCokernelKilling
variable {K : Type} [Field K] {d : ℕ} [NeZero d]
variable {ι : Type}
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution {τ : Type} (σ : K →+* K) (om oms : ι → K) (r : ι) (L : ZMod d → MvPowerSeries τ K) :
    (∑ s : ZMod d, if s.val % 2 = 0 then C (σ^[s.val] (oms r)) * L s else 0) =
      ∑ s : ZMod d, C (pXY σ om oms (false, r) s) * L s := by
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : s.val % 2 = 0 <;> simp [pXY, h]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
