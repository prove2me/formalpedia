-- Prove2me | solution 1 for ConnesGreen.canonical_selected_covariance_le_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:01:42.573825+00:00
-- url     : https://prove2.me/submissions/219f0d95-a86a-496c-a907-da9380d8c8e2

import Theorems.Thm_ConnesGreen_canonical_total_covariance_le_small_support
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem canonical_negative_analysis_partition (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) (h : Physical t) :
    ‖(ContinuousLinearMap.adjoint (canonicalSelectedSynthesis t ht S)) h‖ ^ 2 +
      ‖(ContinuousLinearMap.adjoint (canonicalBackgroundSynthesis t ht S)) h‖ ^ 2 =
      ‖(ContinuousLinearMap.adjoint (canonicalNegativeSynthesis t ht)) h‖ ^ 2 := by
  rw [canonicalSelectedSynthesis, canonicalBackgroundSynthesis, canonicalNegativeSynthesis,
    columnSynthesis_adjoint_norm_sq, columnSynthesis_adjoint_norm_sq,
    columnSynthesis_adjoint_norm_sq]
  have hs : Summable (fun ρ : CriticalZeros =>
      ‖⟪negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ, h⟫_ℂ‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (fun ρ => ?_) ((canonical_actor_columns_summable t ht).2.mul_right (‖h‖ ^ 2))
    simpa only [mul_pow] using
      pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℂ)
          (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) h) 2
  exact hs.tsum_subtype_add_tsum_subtype_compl (S : Set CriticalZeros)

theorem canonical_negative_covariance_partition (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) :
    canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint =
      canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint +
        canonicalBackgroundSynthesis t ht S ∘L (canonicalBackgroundSynthesis t ht S).adjoint := by
  have he := (ext_inner_map
    (canonicalNegativeSynthesis t ht ∘L (canonicalNegativeSynthesis t ht).adjoint).toLinearMap
    (canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint +
      canonicalBackgroundSynthesis t ht S ∘L (canonicalBackgroundSynthesis t ht S).adjoint).toLinearMap).mp
    (fun h => by
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply, inner_add_left]
      rw [← ContinuousLinearMap.adjoint_inner_right (canonicalNegativeSynthesis t ht)
          ((canonicalNegativeSynthesis t ht).adjoint h) h,
        ← ContinuousLinearMap.adjoint_inner_right (canonicalSelectedSynthesis t ht S)
          ((canonicalSelectedSynthesis t ht S).adjoint h) h,
        ← ContinuousLinearMap.adjoint_inner_right (canonicalBackgroundSynthesis t ht S)
          ((canonicalBackgroundSynthesis t ht S).adjoint h) h]
      simp only [inner_self_eq_norm_sq_to_K]
      exact_mod_cast (canonical_negative_analysis_partition t ht S h).symm)
  apply ContinuousLinearMap.ext
  intro h
  exact LinearMap.congr_fun he h

/-- The restored complement is a positive covariance, not an unsigned surrogate. -/
theorem canonical_background_covariance_positive (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros) :
    (canonicalBackgroundSynthesis t ht S ∘L
      (canonicalBackgroundSynthesis t ht S).adjoint).IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint _

theorem solution (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) (S : Finset CriticalZeros) :
    canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint ≤
      canonicalPositiveCovariance T hT := by
  have ht := ConnesGreen.canonical_total_covariance_le_small_support T hT hTr
  rw [canonical_negative_covariance_partition T hT S] at ht
  exact (le_add_of_nonneg_right ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (canonical_background_covariance_positive T hT S))).trans ht
