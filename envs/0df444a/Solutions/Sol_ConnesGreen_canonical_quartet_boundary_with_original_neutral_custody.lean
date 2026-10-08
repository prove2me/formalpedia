-- Prove2me | solution 1 for ConnesGreen.canonical_quartet_boundary_with_original_neutral_custody
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T06:46:57.502063+00:00
-- url     : https://prove2.me/submissions/f89bf1b9-cbd5-4121-8528-3e4a13c5d0d6

import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Theorems.Thm_ConnesGreen_RG0Integration_exists_original_neutral_window_inclusion
import Theorems.Thm_ConnesGreen_canonical_quartet_last_inner_half_window
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_original_quartet
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem positive_helper (t : ℝ) (ht : 0 < t)
    (S : Finset CriticalZeros)
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S) :
    0 ≤ canonicalPositiveCovariance t ht -
      canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint := by
  have hs : IsSelfAdjoint (canonicalPositiveCovariance t ht) := by
    unfold canonicalPositiveCovariance
    exact (ContinuousLinearMap.isPositive_self_comp_adjoint _).isSelfAdjoint
  apply sub_nonneg.mpr
  apply (covariance_le_iff_original_tests t ht _ hs (canonicalSelectedSynthesis t ht S)).mpr
  intro g hg
  have hq := (canonical_picard_half_iff_original_selected_tests t ht S).mp hhalf g hg
  have hp := (canonicalPositiveSynthesis t ht).adjoint.apply_norm_sq_eq_inner_adjoint_left
    (sourceEmbed t (problemOneL g))
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp
  change ‖(canonicalPositiveSynthesis t ht).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 =
    RCLike.re ⟪canonicalPositiveCovariance t ht (sourceEmbed t (problemOneL g)),
      sourceEmbed t (problemOneL g)⟫_ℂ at hp
  linarith
theorem solution (ρ : CriticalZeros)
    (hoff : ρ.1.re ≠ 1 / 2) :
    ∃ c : ℝ, positiveSupportRadius ≤ c ∧
      (∀ T : ℝ, ∀ hT : 0 < T,
        ((1 / 2 : ℝ) • (1 : ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ) →L[ℂ]
          ℓ²({τ : CriticalZeros // τ ∈ quartet ρ}, ℂ)) ≤
            canonicalPicardMarker T hT (quartet ρ) ↔ T ≤ c)) ∧
      ∀ t T : ℝ, ∀ ht : 0 < t, ∀ hT : 0 < T, t ≤ T → T ≤ c →
        ∃ U : Physical t →ₗᵢ[ℂ] Physical T,
          (∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
            U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g)) ∧
          ∀ x : Physical t,
            (canonicalPositiveCovariance t ht -
              canonicalSelectedSynthesis t ht (quartet ρ) ∘L
                (canonicalSelectedSynthesis t ht (quartet ρ)).adjoint) x = 0 ↔
            (canonicalPositiveCovariance T hT -
              canonicalSelectedSynthesis T hT (quartet ρ) ∘L
                (canonicalSelectedSynthesis T hT (quartet ρ)).adjoint) (U x) = 0 := by
  obtain ⟨c, hrc, hcut⟩ := canonical_quartet_last_inner_half_window ρ hoff
  refine ⟨c, hrc, hcut, ?_⟩
  intro t T ht hT htT hTc
  exact RG0Integration.exists_original_neutral_window_inclusion t T ht hT htT (quartet ρ)
    (positive_helper T hT (quartet ρ) ((hcut T hT).mpr hTc))
