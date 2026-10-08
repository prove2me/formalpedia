-- Prove2me | solution 1 for ConnesGreen.canonicalRegularizedMarker_window_antitone
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T23:32:28.524707+00:00
-- url     : https://prove2.me/submissions/df926396-11e5-4c86-b316-82c6d2ae5772

import Theorems.Thm_ConnesGreen_exists_original_window_actor_inclusion
import Theorems.Thm_WeilDefect_MarkerStability_regularized_marker_isometric_compression
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
theorem solution (t T : ℝ) (ht : 0 < t)
    (hT : 0 < T) (htT : t ≤ T) (S : Finset CriticalZeros) (ε : ℝ) (hε : 0 < ε) :
    canonicalRegularizedMarker T hT S ε ≤ canonicalRegularizedMarker t ht S ε := by
  obtain ⟨U, _, _, hP, hM⟩ := exists_original_window_actor_inclusion t T ht hT htT S
  have h := regularized_marker_isometric_compression U
    (canonicalPositiveSynthesis T hT) (canonicalSelectedSynthesis T hT S) ε hε
  rw [hP, hM] at h
  exact h
