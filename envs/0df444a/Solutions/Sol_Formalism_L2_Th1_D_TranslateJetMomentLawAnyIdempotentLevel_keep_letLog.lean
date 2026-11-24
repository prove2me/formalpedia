-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.keep_letLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:25.213911+00:00
-- url     : https://prove2.me/submissions/a7d80760-74bf-4c5d-ae80-2165c754d2b0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_parity_sub_two_mul
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_coeff_keep
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
namespace Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
theorem _root_.solution {l d : ℕ} [NeZero d] (hd : Even d) (j : ZMod d) :
    keep (fun s : ZMod d => (s.val % 2 = 0 ↔ j.val % 2 = 0)) (letLog (K := K) l j) =
      letLog l j := by
  ext n
  rw [coeff_keep]
  split_ifs with h
  · rfl
  · symm
    push_neg at h
    obtain ⟨x, hx, hPx⟩ := h
    show (∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (j - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0) = 0
    refine Finset.sum_eq_zero fun e _ => if_neg ?_
    rintro rfl
    have hx' : j - 2 * (e : ZMod d) = x := by
      by_contra hne
      rw [Finsupp.single_apply, if_neg hne] at hx
      exact hx rfl
    have hp := parity_sub_two_mul hd j e
    rw [hx'] at hp
    omega
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
