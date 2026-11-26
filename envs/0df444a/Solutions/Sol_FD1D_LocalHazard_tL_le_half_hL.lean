-- Prove2me | solution 1 for FD1D.LocalHazard.tL_le_half_hL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:08.597708+00:00
-- url     : https://prove2.me/submissions/1062a02c-40cc-463e-a0a9-4c8f8e2986a5

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_hL_eq_h_add_V_add_w
import Theorems.Thm_FD1D_LocalHazard_abs_w_le_V_add_half_h
import Theorems.Thm_FD1D_LocalHazard_tL_eq

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) (ht : t a p h x y ≤ h / 2) :
    tL a p h x y ≤ hL a h x y / 2 := by
  have hw := abs_w_le_V_add_half_h (x := x) (y := y) ha hh
  have hw' : w a h x y ≤ V a h x y + h / 2 :=
    le_trans (le_abs_self _) hw
  rw [tL_eq ha, hL_eq_h_add_V_add_w]
  linarith
end FD1D.LocalHazard
