-- Prove2me | solution 1 for Eden.attractorProjection_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:09.29246+00:00
-- url     : https://prove2.me/submissions/9be82ad4-572c-483a-9454-3c1494a1842c

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
import Theorems.Thm_Eden_discScale_radius_bound

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (p : PhaseSpace) : attractorProjection p ∈ attractor := by
  refine ⟨discScale_radius_bound (p 0) (p 1), discScale_radius_bound (p 2) (p 3), rfl⟩
end Eden
