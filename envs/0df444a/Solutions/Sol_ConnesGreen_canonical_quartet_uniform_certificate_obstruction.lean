-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_uniform_certificate_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T00:02:17.71075+00:00
-- url     : https://prove2.me/submissions/50b7f5ef-6f21-42a0-8db9-048a076b8636

import Theorems.Thm_ConnesGreen_canonical_selected_negative_uniform_certificate_obstruction
import Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Theorems.Thm_ConnesGreen_canonical_signed_actor_arithmetic
import Definitions.Def_ConnesGreen_finite_selected_correction
import Definitions.Def_ConnesGreen_original_quartet
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Complex ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen
open WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

private theorem partition_helper (t : ℝ) (ht : 0 < t)
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


theorem solution
    (ρ : CriticalZeros) (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤
            canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      ∀ T : ℝ, ∀ hT : 0 < T, c < T →
        ∃ g : ℝ → ℂ, SupportedTest T g ∧
          ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
            (sourceEmbed T (problemOneL g))‖ ^ 2 <
              -(weilDistribution (conv g (starInv g))).re ∧
          ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
            ∀ F : Finset CriticalZeros,
              ¬ 0 ≤ canonicalFiniteSelectedCorrection T hT (quartet ρ) F δ := by
  obtain ⟨c, hc, hcut⟩ := canonical_quartet_last_inner_half_window ρ hoff
  refine ⟨c, hc, hcut, ?_⟩
  intro T hT hcT
  have hn : ¬ ∀ g : ℝ → ℂ, SupportedTest T g →
      0 ≤ ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
        ‖(canonicalSelectedSynthesis T hT (quartet ρ)).adjoint
          (sourceEmbed T (problemOneL g))‖ ^ 2 := by
    intro htests
    have hh := (canonical_picard_half_iff_original_selected_tests T hT (quartet ρ)).mpr htests
    exact (not_le_of_gt hcT) ((hcut T hT).mp hh)
  push Not at hn
  obtain ⟨g, hg, hneg⟩ := hn
  have ha := canonical_signed_actor_arithmetic T hT g hg
  have hp := partition_helper T hT (quartet ρ) (sourceEmbed T (problemOneL g))
  have hb : ‖(canonicalBackgroundSynthesis T hT (quartet ρ)).adjoint
      (sourceEmbed T (problemOneL g))‖ ^ 2 <
      -(weilDistribution (conv g (starInv g))).re := by
    linarith
  exact ⟨g, hg, hb, canonical_selected_negative_uniform_certificate_obstruction
    T hT (quartet ρ) (sourceEmbed T (problemOneL g)) hneg⟩
