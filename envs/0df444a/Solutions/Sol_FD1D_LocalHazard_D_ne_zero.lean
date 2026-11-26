-- Prove2me | solution 1 for FD1D.LocalHazard.D_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:54:30.819687+00:00
-- url     : https://prove2.me/submissions/759ca05a-8969-4772-9452-a0e2ff801685

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_D_pos

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a : ℝ} {x y : ℕ} (ha : 0 < a) (hne : x + y ≠ 0) :
    D a x y ≠ 0 :=
  (D_pos ha hne).ne'
end FD1D.LocalHazard
