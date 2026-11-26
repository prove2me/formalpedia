-- Prove2me | solution 1 for Eden.norm_planeProjection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:57:10.487894+00:00
-- url     : https://prove2.me/submissions/b46469ba-be5a-4645-b4a8-3f885bf30885

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
import Theorems.Thm_Eden_norm_planeProjection
import Theorems.Thm_P2M_Eden_radius__le_norm_83bb5ee710e2
import Theorems.Thm_P2M_Eden_radius__le_norm_a59aead72dbe


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (j : Fin 2) (p : PhaseSpace) :
    ‖planeProjection j p‖ ≤ ‖p‖ := by
  rw [norm_planeProjection]
  fin_cases j
  · exact radius₁_le_norm p
  · exact radius₂_le_norm p
end Eden
