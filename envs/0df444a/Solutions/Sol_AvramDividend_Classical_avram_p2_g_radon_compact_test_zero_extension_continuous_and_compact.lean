-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_compact_test_zero_extension_continuous_and_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:00:27.600884+00:00
-- url     : https://prove2.me/submissions/71caed62-e280-4d88-8e9a-beea53239615

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology

/-- Zero extension transfers a compact negative-mark test to the
    original real mark space while retaining continuity and support. -/
theorem solution
    (f : CompactlySupportedContinuousMap {x : ℝ // x < 0} ℝ) :
    Continuous (Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ) (fun x => f x) 0) ∧
    HasCompactSupport (Function.extend (Subtype.val : {x : ℝ // x < 0} → ℝ) (fun x => f x) 0) := by
  constructor
  · exact HasCompactSupport.continuous_extend_zero
      (isOpen_Iio : IsOpen (Iio (0 : ℝ))) f.continuous f.hasCompactSupport
  · exact f.hasCompactSupport.extend_zero continuous_subtype_val
