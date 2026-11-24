-- Prove2me | solution 1 for Formalism.REAL.integrable_lie_derivative_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:43:48.27194+00:00
-- url     : https://prove2.me/submissions/f4c4579f-ac59-4f47-a6a7-24247f8ee233

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_cutoff_profile_eq_one
import Theorems.Thm_Formalism_REAL_log_frobenius_nonneg
import Theorems.Thm_Formalism_REAL_weight_profile_nonneg
import Theorems.Thm_Formalism_REAL_weight_profile_le_exp
import Theorems.Thm_Formalism_REAL_integrable_weighted_norm_sq
import Theorems.Thm_Formalism_REAL_sum_weighted_lie_derivative_bound
import Theorems.Thm_Formalism_REAL_integrable_of_monotone_bounded
import Theorems.Thm_Formalism_REAL_monotone_cutoff_in_radius
import Theorems.Thm_Formalism_REAL_cutoff_eventually_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace Formalism.REAL
theorem _root_.solution (hl : HhLip) (hz : IntRdZero) {a : ℝ} (ha : 0 ≤ a)
    {u : Matrix (Fin n) (Fin n) ℂ → ℂ} (hu : SmoothOnG ε u)
    (hu2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2) (muG ε))
    (hT2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2)
      (muG ε)) (i j : Fin n) :
    Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
      (muG ε) := by
  have hv := smooth_lie_derivative i j hu
  refine integrable_of_monotone_bounded (F := fun N g => weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2)
    (fun N => integrable_weighted_norm_sq hl a (by positivity) hv)
    (fun N g => mul_nonneg (weight_profile_nonneg _ _ _) (by positivity)) ?_ ?_ ?_ (aestronglyMeasurable_weighted_norm_sq a hv)
    (B := ∑ i, ∑ j, ((2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j) ^ 2 *
          ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖u (toM g)‖ ^ 2 ∂(muG ε) +
        ∫ g : UJ ε, Real.exp (2 * a * hh (toM g)) * ‖signedCasimirDifference ε u (toM g)‖ ^ 2 ∂(muG ε)) ?_
  · intro g N M h
    have h0 := log_frobenius_nonneg g.2
    have hm := monotone_cutoff_in_radius h0 h
    have p0 := cutoff_profile_eq_one (hh (toM g) / ((N : ℝ) + 1))
    simp only [weightProfileAlt]
    have : radialCutoff ((N : ℝ) + 1) (hh (toM g)) ^ 2 ≤ radialCutoff ((M : ℝ) + 1) (hh (toM g)) ^ 2 := by
      unfold radialCutoff at hm p0 ⊢
      exact pow_le_pow_left₀ p0 hm 2
    gcongr
  · intro g
    obtain ⟨N, hN⟩ := cutoff_eventually_one (hh (toM g))
    refine ⟨N, ?_⟩
    simp only [weightProfileAlt, hN N le_rfl]
    ring
  · intro N g
    show weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ≤
      Real.exp (2 * a * hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2
    gcongr
    exact weight_profile_le_exp _ _ _
  · intro N
    have h2 := sum_weighted_lie_derivative_bound hl hz ha (R := (N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)]) hu hu2 hT2
    refine le_trans ?_ h2
    have hnn : ∀ i' j', 0 ≤ ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) *
        ‖Eab ε i' j' u (toM g)‖ ^ 2 ∂(muG ε) := fun i' j' =>
      integral_nonneg fun g => mul_nonneg (weight_profile_nonneg _ _ _) (by positivity)
    calc ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j u (toM g)‖ ^ 2 ∂(muG ε)
        ≤ ∑ j', ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i j' u (toM g)‖ ^ 2
            ∂(muG ε) :=
          Finset.single_le_sum (f := fun j' => ∫ g : UJ ε, weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) *
            ‖Eab ε i j' u (toM g)‖ ^ 2 ∂(muG ε)) (fun j' _ => hnn i j') (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', ∫ g : UJ ε,
            weightProfileAlt a ((N : ℝ) + 1) (hh (toM g)) * ‖Eab ε i' j' u (toM g)‖ ^ 2 ∂(muG ε))
          (fun i' _ => Finset.sum_nonneg fun j' _ => hnn i' j') (Finset.mem_univ i)
end Formalism.REAL
