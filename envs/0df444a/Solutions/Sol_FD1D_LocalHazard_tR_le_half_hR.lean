-- Prove2me | solution 1 for FD1D.LocalHazard.tR_le_half_hR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:55.676184+00:00
-- url     : https://prove2.me/submissions/190517b1-3675-46b7-9770-52f9f98f19db

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_hR_eq_h_add_V_sub_w
import Theorems.Thm_FD1D_LocalHazard_abs_w_le_V_add_half_h
import Theorems.Thm_FD1D_LocalHazard_tR_eq

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    tR a p h x y ≤ hR a h x y / 2 := by
  have hw := abs_w_le_V_add_half_h (x := x) (y := y) ha hh
  have hw' : -w a h x y ≤ V a h x y + h / 2 := by
    calc
      -w a h x y ≤ |-w a h x y| := le_abs_self _
      _ = |w a h x y| := abs_neg _
      _ ≤ V a h x y + h / 2 := hw
  rw [tR_eq ha, hR_eq_h_add_V_sub_w]
  linarith
end FD1D.LocalHazard
