-- Prove2me | solution 1 for ConnesGreen.canonicalPicardMarker_window_antitone
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:38:34.866702+00:00
-- url     : https://prove2.me/submissions/eacd1ca5-41ce-4670-9c64-9195f0212fdd

import Theorems.Thm_ConnesGreen_canonicalRegularizedMarker_window_antitone
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
theorem solution (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros) :
    canonicalPicardMarker T hT S ≤ canonicalPicardMarker t ht S := by
  apply le_of_tendsto_of_tendsto (canonicalPicardMarker_spec T hT S).2.2.2
    (canonicalPicardMarker_spec t ht S).2.2.2
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact canonicalRegularizedMarker_window_antitone t T ht hT htT S ε hε
