-- Prove2me | solution 1 for ConnesGreen.RG0Integration.original_endpoint_no_strict_half_margin
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:48:07.820799+00:00
-- url     : https://prove2.me/submissions/0e25fc6b-0af6-48e5-b974-85dc1b8105b3

import Theorems.Thm_ConnesGreen_RG0Integration_original_picard_outer_no_strict_half_margin
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section
theorem solution
    (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros)
    (hbad : ∀ T : ℝ, ∀ hT : 0 < T, c < T →
      ¬ (1/2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
        ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker T hT S)
    (a : ℝ) (ha : (1/2 : ℝ) < a) :
    ¬ a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc.le S := by
  exact ConnesGreen.RG0Integration.original_picard_outer_no_strict_half_margin
    c hc S (canonicalSupportRightMarker c hc.le S)
    (canonicalSupportRightMarker_spec c hc.le S).2.2.2 hbad a ha
