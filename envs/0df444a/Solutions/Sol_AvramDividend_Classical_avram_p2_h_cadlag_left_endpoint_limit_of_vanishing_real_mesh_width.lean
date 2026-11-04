-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_left_endpoint_limit_of_vanishing_real_mesh_width
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:48:29.610365+00:00
-- url     : https://prove2.me/submissions/52ba5cd8-e4a7-497d-b6d3-a73f1cfc1c85

import Mathlib.Topology.Instances.NNReal.Lemmas

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- If the right endpoints converge and the real widths vanish,
then the left endpoints converge to the same compactness limit. -/
theorem solution
    (a b : ℕ → ℝ≥0) (t : ℝ≥0)
    (hb : Tendsto b atTop (𝓝 t))
    (hgap : Tendsto (fun n => (b n : ℝ) - (a n : ℝ))
      atTop (𝓝 (0 : ℝ))) :
    Tendsto a atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  have hb' : Tendsto (fun n : ℕ => (b n : ℝ))
      atTop (𝓝 (t : ℝ)) := NNReal.tendsto_coe.mpr hb
  have heq : (fun n : ℕ => (b n : ℝ) - ((b n : ℝ) - (a n : ℝ))) =
      (fun n : ℕ => (a n : ℝ)) := by
    funext n
    ring
  simpa only [heq, sub_zero] using hb'.sub hgap
