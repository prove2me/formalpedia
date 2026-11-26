-- Prove2me | solution 1 for FD1D.LocalHazard.w_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:10.739795+00:00
-- url     : https://prove2.me/submissions/ec4b9cc7-f0e7-4f1f-befe-27241e86d55c

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_D_ne_zero
import Theorems.Thm_FD1D_LocalHazard_N_add_two_mul_a_ne_zero
import Theorems.Thm_FD1D_LocalHazard_V_eq
import Theorems.Thm_FD1D_LocalHazard_w_eq

set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    w a h x y ^ 2 =
      N x y / (N x y + 2 * a) * V a h x y * (h + V a h x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [w, V, hL, hR, N]
  · have hD := D_ne_zero ha hne
    have hNa := N_add_two_mul_a_ne_zero ha x y
    rw [w_eq ha, V_eq ha]
    field_simp [hD, hNa]
    unfold D N
    ring
end FD1D.LocalHazard
