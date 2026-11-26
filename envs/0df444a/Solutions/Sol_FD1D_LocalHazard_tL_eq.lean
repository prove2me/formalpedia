-- Prove2me | solution 1 for FD1D.LocalHazard.tL_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:02.989676+00:00
-- url     : https://prove2.me/submissions/560b9a56-fb89-424a-a74b-fa08d1b6c332

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_qL_add_qR
import Theorems.Thm_FD1D_LocalHazard_b_eq_neg_two_mul_a_mul_w
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    tL a p h x y = t a p h x y / 2 + w a h x y := by
  have hqsum := qL_add_qR (a := a) (h := h) (x := x) (y := y) ha
  have hbw := b_eq_neg_two_mul_a_mul_w (a := a) (h := h) (x := x) (y := y) ha
  simp only [b] at hbw
  simp only [tL, t]
  field_simp [ha.ne']
  nlinarith
end FD1D.LocalHazard
