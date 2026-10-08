-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_half_iff_original_jump_budget
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:50:19.658377+00:00
-- url     : https://prove2.me/submissions/1da129d7-4757-481d-a4b7-2ef92cd1e8cd

import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section
theorem solution (c : ℝ) (hc : 0 < c)
    (S : Finset CriticalZeros) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc.le S ↔
    canonicalPicardMarker c hc S - canonicalSupportRightMarker c hc.le S ≤
      canonicalPicardMarker c hc S - (1 / 2 : ℝ) • 1 := by
  exact sub_le_sub_iff_left _ |>.symm
