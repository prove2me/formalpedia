-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.comb_zXY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:15.08583+00:00
-- url     : https://prove2.me/submissions/58aa726c-1686-4b20-8026-7b45f4aa7a5c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_dual1
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_zXY_eq
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
theorem _root_.solution [Fintype ι] [DecidableEq ι] (hd : Even d) (l : ℕ) (σ : K →+* K) {om oms : ι → K}
    (hfix : ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) (hT : TrDual d σ om oms)
    (x : Bool × ι) :
    (∑ s : ZMod d, C (pXY σ om oms x s) * zXY l σ om oms s) = at1 x (lgF K l) := by
  simp only [zXY_eq, Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, ← map_sum, dual1 hd σ hfix hT]
  simp
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
