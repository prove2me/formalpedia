-- Prove2me | solution 1 for ConnesGreen.canonical_support_right_le_inner
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:48:05.840391+00:00
-- url     : https://prove2.me/submissions/38fa0128-9f14-4f00-a5a2-415b677478d3

import Theorems.Thm_ConnesGreen_canonicalPicardMarker_window_antitone
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex ConnesRZ ConnesRZFrontier ConnesGreen
open scoped InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section
theorem solution (c : ℝ) (hc : 0 < c) (S : Finset CriticalZeros) :
    canonicalSupportRightMarker c hc.le S ≤ canonicalPicardMarker c hc S := by
  apply (canonicalSupportRightMarker_spec c hc.le S).2.2.1.2
  rintro _ ⟨T, hTc, rfl⟩
  have hT : 0 < T := hc.trans hTc
  change positiveWindowPicardMarker T S ≤ canonicalPicardMarker c hc S
  rw [positiveWindowPicardMarker_eq T hT]
  exact canonicalPicardMarker_window_antitone c T hc hT hTc.le S
