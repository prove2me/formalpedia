-- Prove2me | solution 1 for ConnesGreen.selected_signed_covariance_nonnegative_of_half
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T06:46:38.894986+00:00
-- url     : https://prove2.me/submissions/d0da1414-c9b8-4fe8-94f7-80246b2d0f89

import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Theorems.Thm_ConnesGreen_canonical_picard_half_iff_original_selected_tests
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_original_quartet
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesRZQuartet ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem solution (t : ℝ) (ht : 0 < t)
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
