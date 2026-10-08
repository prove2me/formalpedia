-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_half_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:17:22.110413+00:00
-- url     : https://prove2.me/submissions/2930c41a-9a1d-4d15-af65-3ded2236ac36

import Theorems.Thm_ConnesGreen_canonical_picard_half_small_support
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (c : ℝ) (hc : 0 ≤ c)
    (hcr : c < positiveSupportRadius) (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S  := by
  let T := (c + positiveSupportRadius) / 2
  have hT : 0 < T := by dsimp [T]; linarith
  have hcT : c < T := by dsimp [T]; linarith
  have hTr : T ≤ positiveSupportRadius := by dsimp [T]; linarith
  have hl : canonicalPicardMarker T hT S ≤ canonicalSupportRightMarker c hc S := by
    have h := (canonicalSupportRightMarker_spec c hc S).2.2.1.1 ⟨T, hcT, rfl⟩
    simpa only [positiveWindowPicardMarker_eq T hT S] using h
  exact (ConnesGreen.canonical_picard_half_small_support T hT hTr S).trans hl
