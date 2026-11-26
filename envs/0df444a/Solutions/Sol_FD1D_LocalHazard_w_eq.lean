-- Prove2me | solution 1 for FD1D.LocalHazard.w_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:39.150059+00:00
-- url     : https://prove2.me/submissions/398d3c30-022a-4755-87bc-39a6861dcae7

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_D_ne_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    w a h x y =
      h * N x y * ((y : ℝ) - (x : ℝ)) / (2 * D a x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [w, hL, hR, D, N]
  · have hD := D_ne_zero ha hne
    simp only [w, hL, hR, if_neg hne]
    field_simp [hD]
    ring
end FD1D.LocalHazard
