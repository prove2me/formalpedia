-- Prove2me | solution 1 for Eden.empty_not_uniformlyAttractsBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:57.318316+00:00
-- url     : https://prove2.me/submissions/3e6ea561-b824-4316-9d08-80d7fbc0d28d

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_uniformlyAttractsBounded_nonempty

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) :
    ¬UniformlyAttractsBounded c (∅ : Set PhaseSpace) := by
  intro h
  exact Set.not_nonempty_empty (uniformlyAttractsBounded_nonempty h)
end Eden
