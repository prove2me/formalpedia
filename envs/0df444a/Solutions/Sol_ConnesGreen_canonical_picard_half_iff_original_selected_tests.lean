-- Prove2me | solution 1 for ConnesGreen.canonical_picard_half_iff_original_selected_tests
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:23:42.314605+00:00
-- url     : https://prove2.me/submissions/f71fddc9-3b92-4e17-aedc-709a7ef31571

import Theorems.Thm_ConnesGreen_covariance_le_iff_original_tests
import Theorems.Thm_ConnesGreen_RG0Integration_original_picard_half_iff_covariance
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
theorem solution (T : ℝ) (hT : 0 < T)
    (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S ↔
    ∀ g : ℝ → ℂ, SupportedTest T g →
      0 ≤ ‖(canonicalPositiveSynthesis T hT).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 -
        ‖(canonicalSelectedSynthesis T hT S).adjoint (sourceEmbed T (problemOneL g))‖ ^ 2 := by
  rw [ConnesGreen.RG0Integration.original_picard_half_iff_covariance,
    canonicalPositiveCovariance, covariance_le_iff_original_tests T hT _
      (ContinuousLinearMap.isPositive_self_comp_adjoint
        (canonicalPositiveSynthesis T hT)).isSelfAdjoint _]
  apply forall_congr'
  intro g
  apply imp_congr_right
  intro hg
  have hp := (canonicalPositiveSynthesis T hT).adjoint.apply_norm_sq_eq_inner_adjoint_left
    (sourceEmbed T (problemOneL g))
  simp only [ContinuousLinearMap.adjoint_adjoint] at hp
  change (_ ≤ RCLike.re ⟪(canonicalPositiveSynthesis T hT ∘L
    (canonicalPositiveSynthesis T hT).adjoint) (sourceEmbed T (problemOneL g)),
    sourceEmbed T (problemOneL g)⟫_ℂ) ↔ _
  rw [← hp]
  exact sub_nonneg.symm

