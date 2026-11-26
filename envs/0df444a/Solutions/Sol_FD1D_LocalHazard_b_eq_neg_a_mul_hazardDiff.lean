-- Prove2me | solution 1 for FD1D.LocalHazard.b_eq_neg_a_mul_hazardDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:12.744512+00:00
-- url     : https://prove2.me/submissions/a97dbe45-0637-40f4-a67c-3ac308e9f716

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
    b a h x y = -a * (hL a h x y - hR a h x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    simp [b, qL, qR, q, dL, dR, hL, hR, N]
  · have hD := D_ne_zero ha hne
    simp only [b, qL, qR, q, dL, dR, hL, hR, if_neg hne]
    field_simp [hD, D, N]
    ring
end FD1D.LocalHazard
