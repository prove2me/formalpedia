-- Prove2me | solution 1 for FD1D.LocalHazard.V_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:46.946694+00:00
-- url     : https://prove2.me/submissions/aeb0b1c1-37e7-482b-b18c-940053d01679

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
    V a h x y =
      h * ((x : ℝ) - (y : ℝ)) ^ 2 / (2 * D a x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [V, hL, hR, D, N]
  · have hD := D_ne_zero ha hne
    simp only [V, hL, hR, if_neg hne]
    field_simp [hD]
    unfold D N
    ring
end FD1D.LocalHazard
