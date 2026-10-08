-- Prove2me | solution 1 for ConnesGreen.canonical_regularized_half_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:04:09.539979+00:00
-- url     : https://prove2.me/submissions/07a95edd-b429-40c0-827d-6067e80f2da2

import Theorems.Thm_ConnesGreen_canonical_selected_covariance_le_small_support
import Theorems.Thm_ConnesGreen_RG0Integration_original_picard_half_iff_covariance
import Theorems.Thm_ConnesGreen_canonicalPicardMarker_lower_iff_all_regularized
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem solution (T : ℝ) (hT : 0 < T)
    (hTr : T ≤ positiveSupportRadius) (S : Finset CriticalZeros) :
    ∀ ε : ℝ, 0 < ε → (1 / 2 : ℝ) •
      (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalRegularizedMarker T hT S ε  := by
  have hp := (ConnesGreen.RG0Integration.original_picard_half_iff_covariance T hT S).mpr
    (ConnesGreen.canonical_selected_covariance_le_small_support T hT hTr S)
  exact (ConnesGreen.canonicalPicardMarker_lower_iff_all_regularized T hT S (1/2)).mp hp

