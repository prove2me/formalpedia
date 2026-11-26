-- Prove2me | solution 1 for FD1D.LocalHazard.N_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:24.978975+00:00
-- url     : https://prove2.me/submissions/511b647a-decc-4bf8-b688-a15c0215dabe

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_pos

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {x y : ℕ} (hne : x + y ≠ 0) : N x y ≠ 0 :=
  (N_pos hne).ne'
end FD1D.LocalHazard
