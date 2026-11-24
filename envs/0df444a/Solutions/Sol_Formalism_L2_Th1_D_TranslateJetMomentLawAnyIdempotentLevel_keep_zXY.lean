-- Prove2me | solution 1 for Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel.keep_zXY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:31:28.820619+00:00
-- url     : https://prove2.me/submissions/597d14a4-194b-4652-bf69-cc5696419a6b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_EqZeroOfPowEqOne
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FirstMomentIdempotentLaw
import Theorems.Thm_Formalism_L2_Th1_D_TranslateJetMomentLawAnyIdempotentLevel_coeff_keep
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series
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
theorem _root_.solution {l d : ℕ} [NeZero d] {ι : Type} [Fintype ι] (σ : K →+* K) (om oms : ι → K)
    (j : ZMod d) :
    keep (fun x : Bool × ι => (x.1 = false ↔ j.val % 2 = 0)) (zXY l σ om oms j) =
      zXY l σ om oms j := by
  classical
  ext n
  rw [coeff_keep]
  split_ifs with h
  · rfl
  · symm
    simp only [not_forall] at h
    obtain ⟨x, hx, hPx⟩ := h
    unfold zXY
    split_ifs with hj
    · rw [map_sum]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [MvPowerSeries.coeff_C_mul, Formalism.InvariantFactorPaths.G7.coeff_single_variable_series, if_neg, mul_zero]
      intro hn
      apply hPx
      have hxr : x = (false, r) := by
        by_contra hne
        rw [hn, Finsupp.single_apply, if_neg (Ne.symm hne)] at hx
        exact hx rfl
      subst hxr
      simp [hj]
    · rw [map_sum]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [MvPowerSeries.coeff_C_mul, Formalism.InvariantFactorPaths.G7.coeff_single_variable_series, if_neg, mul_zero]
      intro hn
      apply hPx
      have hxr : x = (true, r) := by
        by_contra hne
        rw [hn, Finsupp.single_apply, if_neg (Ne.symm hne)] at hx
        exact hx rfl
      subst hxr
      simp [hj]
end Formalism.L2.Th1.D.TranslateJetMomentLawAnyIdempotentLevel
