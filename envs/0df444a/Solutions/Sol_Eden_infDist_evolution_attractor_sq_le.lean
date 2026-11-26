-- Prove2me | solution 1 for Eden.infDist_evolution_attractor_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:38.613646+00:00
-- url     : https://prove2.me/submissions/f414b99c-48c2-446e-9df4-b1ddee80de42

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_dist_projection_evolution_sq_le
import Theorems.Thm_Eden_attractorProjection_mem


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W) :
    Metric.infDist (evolution c t p) attractor ^ 2 ≤ attractionBound c M W t := by
  have hd := Metric.infDist_le_dist_of_mem (x := evolution c t p)
    (attractorProjection_mem (evolution c t p))
  have hn : 0 ≤ Metric.infDist (evolution c t p) attractor := Metric.infDist_nonneg
  have hb := dist_projection_evolution_sq_le c ht hM h₁ h₂ hw
  nlinarith
end Eden
