-- Prove2me | solution 1 for CohnElkies.log_normalizedVolumeRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/14a5df85-891a-483a-9e3d-09b7b8a50b92

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
namespace CohnElkies
theorem _root_.solution {d : ℕ} (hd : 0 < d) :
    Real.log (normalizedVolumeRoot d) = normalizedVolumeLog d := by
  unfold normalizedVolumeRoot normalizedVolumeLog
  rw [Real.log_mul
    (Real.rpow_pos_of_pos (unitBallVolume_pos d) _).ne'
    (Real.sqrt_pos.2 (by exact_mod_cast hd)).ne',
    Real.log_rpow (unitBallVolume_pos d),
    Real.log_sqrt (by exact_mod_cast (Nat.zero_le d))]
  ring
end CohnElkies
