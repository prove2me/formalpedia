-- Prove2me | solution 1 for FD1D.LocalHazard.N_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:52:03.180279+00:00
-- url     : https://prove2.me/submissions/31707f75-9faf-43c2-8dbe-0803e4e75ae2

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {x y : ℕ} (hne : x + y ≠ 0) : 0 < N x y := by
  have hxy : 0 < x + y := Nat.pos_of_ne_zero hne
  unfold N
  exact_mod_cast hxy
end FD1D.LocalHazard
