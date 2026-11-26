-- Prove2me | solution 1 for FD1D.LocalHazard.t_div_h_le_half_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:54:51.10298+00:00
-- url     : https://prove2.me/submissions/2eab8e4b-edd8-4ae8-9361-56e741452a38

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_hL_pos
import Theorems.Thm_FD1D_LocalHazard_tL_le_half_hL

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (ht : t a p h x y / h ≤ 1 / 2) :
    tL a p h x y / hL a h x y ≤ 1 / 2 := by
  have ht' : t a p h x y ≤ h / 2 := by
    apply (div_le_iff₀ hh).mp at ht
    linarith
  have hchild : 0 < hL a h x y := hL_pos ha hh
  apply (div_le_iff₀ hchild).2
  have := tL_le_half_hL ha hh.le ht'
  linarith
end FD1D.LocalHazard
