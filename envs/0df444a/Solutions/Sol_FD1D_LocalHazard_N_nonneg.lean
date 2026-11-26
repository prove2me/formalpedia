-- Prove2me | solution 1 for FD1D.LocalHazard.N_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:52:26.558973+00:00
-- url     : https://prove2.me/submissions/37a863e4-b460-4ec8-9595-17265654c525

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution (x y : ℕ) : 0 ≤ N x y := by
  unfold N
  positivity
end FD1D.LocalHazard
