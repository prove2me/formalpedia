-- Prove2me | solution 1 for Eden.attractor_isGlobalAttractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:07:47.427649+00:00
-- url     : https://prove2.me/submissions/53c6f5e5-a66d-4f81-89d1-48df62d1841c

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_attractor_uniformlyAttractsBounded
import Theorems.Thm_Eden_attractor_nonempty
import Theorems.Thm_Eden_evolution_image_attractor
import Theorems.Thm_Eden_isCompact_attractor


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 0 < c) : IsGlobalAttractor c attractor :=
  ⟨attractor_nonempty, isCompact_attractor, (fun _ ht => evolution_image_attractor c ht),
    attractor_uniformlyAttractsBounded hc⟩
end Eden
