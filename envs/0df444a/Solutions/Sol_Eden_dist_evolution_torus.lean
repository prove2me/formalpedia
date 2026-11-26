-- Prove2me | solution 1 for Eden.dist_evolution_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:33.559821+00:00
-- url     : https://prove2.me/submissions/c0dded09-96e3-464e-8571-69d7b35d71a4

import Definitions.Def_Eden_TorusAngles
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_Uniqueness
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Eden_TorusRecurrence
import Theorems.Thm_Eden_evolution_eq_angularRotation_on_torus

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c t : ℝ) {p q : PhaseSpace}
    (hp : p ∈ torus) (hq : q ∈ torus) :
    dist (evolution c t p) (evolution c t q) = dist p q := by
  rw [evolution_eq_angularRotation_on_torus c t hp,
    evolution_eq_angularRotation_on_torus c t hq]
  exact (angularRotation t).dist_map _ _
end Eden
