-- Prove2me | solution 1 for CohnElkies.packingGeometricRoot_eq_normalizedVolumeRoot_div_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/93973778-6aad-40ac-974c-3d5fa6417b10

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_rpow_two_pow_inv_dimension

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) :
    packingGeometricRoot d = normalizedVolumeRoot d / 2 := by
  unfold packingGeometricRoot normalizedVolumeRoot
  rw [Real.div_rpow (unitBallVolume_pos d).le (by positivity),
    rpow_two_pow_inv_dimension hd]
  ring
end CohnElkies
