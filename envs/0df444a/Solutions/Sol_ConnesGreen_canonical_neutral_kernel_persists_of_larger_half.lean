-- Prove2me | solution 1 for ConnesGreen.canonical_neutral_kernel_persists_of_larger_half
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T06:46:56.301997+00:00
-- url     : https://prove2.me/submissions/70c6d84e-afab-4b17-ae3f-37dfd4ac2dfc

import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Theorems.Thm_ConnesGreen_RG0Integration_window_inclusion_original_source_adjoint
import Theorems.Thm_ConnesGreen_RG0Integration_original_neutral_kernel_persists_of_source_compression
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
theorem solution (t T : ℝ) (ht : 0 < t) (hT : 0 < T)
    (htT : t ≤ T) (S : Finset CriticalZeros) (U : Physical t →ₗᵢ[ℂ] Physical T)
    (hU : ∀ g : ℝ → ℂ, ∀ _hg : SupportedTest t g,
      U (sourceEmbed t (problemOneL g)) = sourceEmbed T (problemOneL g))
    (hhalf : (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S) (x : Physical t) :
    (canonicalPositiveCovariance t ht -
      canonicalSelectedSynthesis t ht S ∘L (canonicalSelectedSynthesis t ht S).adjoint) x = 0 ↔
      (canonicalPositiveCovariance T hT -
        canonicalSelectedSynthesis T hT S ∘L (canonicalSelectedSynthesis T hT S).adjoint) (U x) = 0 := by
  have hsource := RG0Integration.window_inclusion_original_source_adjoint t T ht hT htT U hU
  exact RG0Integration.original_neutral_kernel_persists_of_source_compression t T ht hT S U hsource
    (positive_helper T hT S hhalf) x
