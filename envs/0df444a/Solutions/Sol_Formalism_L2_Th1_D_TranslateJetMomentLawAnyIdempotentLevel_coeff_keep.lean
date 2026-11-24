-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.coeff_keep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:37:49.265211+00:00
-- url     : https://prove2.me/submissions/aaa98bb5-9290-47ee-a358-f4a65f8bbbee

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
variable {K : Type} [Field K]
open Classical
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution {τ : Type} (P : τ → Prop) (f : MvPowerSeries τ K)
    (n : τ →₀ ℕ) :
    coeff n (keep P f) = if ∀ x, n x ≠ 0 → P x then coeff n f else 0 := by
  unfold keep
  rw [MvPowerSeries.coeff_rescale]
  split_ifs with h
  · rw [Finsupp.prod, Finset.prod_eq_one, one_mul]
    intro x hx
    rw [if_pos (h x (Finsupp.mem_support_iff.1 hx)), one_pow]
  · push_neg at h
    obtain ⟨x, hx, hPx⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hx), zero_mul]
    rw [if_neg hPx, zero_pow hx]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
