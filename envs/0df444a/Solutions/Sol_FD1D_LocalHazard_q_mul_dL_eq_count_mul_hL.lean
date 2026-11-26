-- Prove2me | solution 1 for FD1D.LocalHazard.q_mul_dL_eq_count_mul_hL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:27.541971+00:00
-- url     : https://prove2.me/submissions/685b3c2c-f682-43d4-a221-5fc1bf2c1f53

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
theorem _root_.solution {a h qParent : ℝ} {x y : ℕ}
    (ha : 0 < a) (hq : qParent = N x y * h) :
    qParent * dL a x y = (x : ℝ) * hL a h x y := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [dL, hL, hq, N]
  · have hD := D_ne_zero ha hne
    rw [hq]
    simp only [dL, hL, if_neg hne]
    field_simp [hD]
end FD1D.LocalHazard
