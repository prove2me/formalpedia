-- Prove2me | solution 1 for Eden.plane_radius_sub_le_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:42.665818+00:00
-- url     : https://prove2.me/submissions/464b7b9c-851d-45af-96e9-ebbf57c3d216

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
import Theorems.Thm_Eden_norm_planeProjection_le
import Theorems.Thm_Eden_planeProjection_sub

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (j : Fin 2) (p q : PhaseSpace) :
    ‖planeProjection j q‖ - ‖planeProjection j p‖ ≤ dist p q := by
  calc
    _ ≤ ‖planeProjection j q - planeProjection j p‖ := norm_sub_norm_le _ _
    _ = ‖planeProjection j (q - p)‖ := by rw [planeProjection_sub]
    _ ≤ ‖q - p‖ := norm_planeProjection_le j (q - p)
    _ = dist p q := by rw [← dist_eq_norm, dist_comm]
end Eden
