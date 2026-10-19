-- Prove2me | solution 2 for CohnElkies.log_normalizedVolumeRoot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:37.699005+00:00
-- url     : https://prove2.me/submissions/415e09fc-14aa-435e-b4e6-c590f3ac7ec2

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


theorem solution {d : ℕ} (hd : 0 < d) :
    Real.log (normalizedVolumeRoot d) = normalizedVolumeLog d := by
  unfold normalizedVolumeRoot normalizedVolumeLog
  have hV := unitBallVolume_pos d
  have hs : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hd)
  rw [Real.log_mul (Real.rpow_pos_of_pos hV _).ne' hs.ne', Real.log_rpow hV,
    Real.log_sqrt (Nat.cast_nonneg d)]
  ring

