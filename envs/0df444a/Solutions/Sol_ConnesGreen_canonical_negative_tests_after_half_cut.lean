-- Prove2me | solution 1 for ConnesGreen.canonical_negative_tests_after_half_cut
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:52:21.830357+00:00
-- url     : https://prove2.me/submissions/443acdc9-dafd-45de-9b01-ef8f54fee801

import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
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

theorem solution (S : Finset CriticalZeros)
    (c : ℝ) (hcut : (∀ T : ℝ, ∀ hT : 0 < T, ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) ↔ T ≤ c))
    (T : ℝ) (hT : 0 < T) (hcT : c < T) :
    ∃ g : ℝ → ℂ, SupportedTest T g ∧
      ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 < 0 ∧
      ‖(canonicalBackgroundSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 <
        -(weilDistribution (conv g (starInv g))).re := by
  classical
  have hn : ¬ ∀ g : ℝ → ℂ, SupportedTest T g →
      0 ≤ ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 := by
    intro htests
    have hh := (canonical_picard_half_iff_original_selected_tests T hT S).mpr htests
    exact (not_le_of_gt hcT) ((hcut T hT).mp hh)
  push Not at hn
  obtain ⟨g, hg, hneg⟩ := hn
  refine ⟨g, hg, hneg, ?_⟩
  have hf := canonical_signed_actor_arithmetic T hT g hg
  have hp := canonical_negative_analysis_partition T hT S (sourceEmbed T (problemOneL g))
  linarith
