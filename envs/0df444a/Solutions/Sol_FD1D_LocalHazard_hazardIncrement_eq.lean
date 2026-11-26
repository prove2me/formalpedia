-- Prove2me | solution 1 for FD1D.LocalHazard.hazardIncrement_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:57:27.109717+00:00
-- url     : https://prove2.me/submissions/87c83366-8e1f-4419-a5b7-40b08e735024

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_N_ne_zero
import Theorems.Thm_FD1D_LocalHazard_D_ne_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ} (ha : 0 < a) :
    (hL a h x y ^ 2 + hR a h x y ^ 2) / 2 - h ^ 2 =
      b a h x y ^ 2 / a ^ 2 *
        ((3 - rho x y ^ 2) / 4 + a / N x y) := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [hL, hR, b, qL, qR, q, dL, dR, rho, N]
  · have hD := D_ne_zero ha hne
    have hN := N_ne_zero hne
    have ha0 := ha.ne'
    simp only [hL, hR, b, qL, qR, q, dL, dR, rho, if_neg hne]
    field_simp [hD, hN, ha0]
    unfold D N
    ring
end FD1D.LocalHazard
