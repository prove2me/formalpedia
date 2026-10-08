-- Prove2me | solution 1 for ConnesGreen.canonical_jump_budget_small_support
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T05:20:13.950998+00:00
-- url     : https://prove2.me/submissions/02f72e92-dae3-431e-af4b-00d60e6b3615

import Theorems.Thm_ConnesGreen_canonical_endpoint_half_small_support
import Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_original_jump_budget
import Definitions.Def_ConnesGreen_small_support_constants
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
theorem solution (c : ℝ) (hc : 0 < c) (hcr : c < positiveSupportRadius) (S : Finset CriticalZeros) :
    canonicalPicardMarker c hc S - canonicalSupportRightMarker c hc.le S ≤
      canonicalPicardMarker c hc S - (1 / 2 : ℝ) • 1 := by
  exact (ConnesGreen.canonical_endpoint_half_iff_original_jump_budget c hc S).mp
    (ConnesGreen.canonical_endpoint_half_small_support c hc.le hcr S)
