-- Prove2me | solution 1 for FD1D.V5.LocalBellman.Normalized.g_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:08.265946+00:00
-- url     : https://prove2.me/submissions/7dfa5146-d001-40ce-a30a-fe00edf14268

import Definitions.Def_FD1D_V5_LocalInvariants
import Definitions.Def_FD1D_V5_LocalBellman

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
open FD1D.V5.LocalBellman.Normalized
namespace FD1D.V5.LocalBellman.Normalized
theorem _root_.solution {s r : ℝ} (hr : -s < r) :
    0 < g s r := by
  unfold g
  linarith
end FD1D.V5.LocalBellman.Normalized
