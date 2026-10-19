-- Prove2me | solution 2 for CohnElkies.packingGeometricRoot_eq_normalizedVolumeRoot_div_two
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:15.681637+00:00
-- url     : https://prove2.me/submissions/e4e17fe0-ccb0-4711-88e1-f48586e7cabd

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology


theorem solution
    {d : ℕ} (hd : 0 < d) :
    packingGeometricRoot d = normalizedVolumeRoot d / 2 := by
  unfold packingGeometricRoot normalizedVolumeRoot
  rw [Real.div_rpow (unitBallVolume_pos d).le (by positivity),
    Real.pow_rpow_inv_natCast (by norm_num) hd.ne']
  ring

