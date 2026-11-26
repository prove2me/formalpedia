-- Prove2me | solution 1 for Eden.infDist_attractor_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:52:42.024982+00:00
-- url     : https://prove2.me/submissions/36110567-9167-42e8-a0ec-7767ca383fa2

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
import Theorems.Thm_Eden_attractorProjection_mem
import Theorems.Thm_Eden_dist_attractorProjection_sq

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (p : PhaseSpace) :
    Metric.infDist p attractor ^ 2 ≤
      max (Real.sqrt (radiusSq₁ p) - Real.sqrt 2) 0 ^ 2 +
      max (Real.sqrt (radiusSq₂ p) - Real.sqrt 2) 0 ^ 2 + p 4 ^ 2 := by
  have hle := Metric.infDist_le_dist_of_mem (x := p) (attractorProjection_mem p)
  have heq := dist_attractorProjection_sq p
  have hn : 0 ≤ Metric.infDist p attractor := Metric.infDist_nonneg
  nlinarith
end Eden
