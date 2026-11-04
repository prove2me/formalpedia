-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_generic_jumpmark_vanish_from_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:32:11.888936+00:00
-- url     : https://prove2.me/submissions/2535330b-e6b8-453d-8fdb-903bf136ec94

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- Any path with actual left limits has jumps vanishing along a strict
approach to a positive time from the left. -/
theorem solution
    (Y : ℝ≥0 → ℝ)
    (hL : ∀ u : ℝ≥0, 0 < u →
      Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)))
    (t : ℝ≥0) (ht : 0 < t) :
    Tendsto (fun u : ℝ≥0 => Y u - Function.leftLim Y u)
      (𝓝[<] t) (𝓝 (0 : ℝ)) := by
  have hleft :
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)) := hL t ht
  have hpre :
      ContinuousWithinAt (Function.leftLim Y) (Iic t) t :=
    continuousWithinAt_leftLim_Iic hleft
  have hpre' :
      Tendsto (Function.leftLim Y) (𝓝[<] t)
        (𝓝 (Function.leftLim Y t)) :=
    hpre.mono_left (nhdsWithin_mono t Set.Iio_subset_Iic_self)
  simpa only [sub_self] using hleft.sub hpre'
