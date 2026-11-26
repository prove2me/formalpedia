-- Prove2me | solution 1 for Eden.unstableRelativeTo_of_unit_plane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:51:42.955715+00:00
-- url     : https://prove2.me/submissions/3d83dfc3-c2ae-4798-a4f5-5ff3ac7cfc7d

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability
import Theorems.Thm_Eden_unstableRelativeTo_of_unit_plane_in
import Theorems.Thm_Eden_radialPerturbation_mem_attractor


set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (j : Fin 2) {K : Set PhaseSpace}
    {s : ℝ} (hs : s ∈ Icc 0 1) (hend : radialPerturbation j 1 s ∈ K)
    (hunit : ∀ q ∈ K, ‖planeProjection j q‖ = 1) :
    UnstableRelativeTo c attractor K :=
  unstableRelativeTo_of_unit_plane_in c j
    (fun _ hr => radialPerturbation_mem_attractor j hr hs) hend hunit
end Eden
