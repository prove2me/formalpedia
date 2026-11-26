-- Prove2me | solution 1 for Eden.attractor_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:48.502384+00:00
-- url     : https://prove2.me/submissions/39f3bde2-1993-4440-90b9-fc63fbd79f6a

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_attractor_subset_of_uniformlyAttractsBounded

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} {C : Set PhaseSpace} (hcompact : IsCompact C)
    (hC : UniformlyAttractsBounded c C) : attractor ⊆ C :=
  attractor_subset_of_uniformlyAttractsBounded hcompact.isClosed hC
end Eden
