-- Prove2me | solution 1 for FD1D.LocalHazard.q_mul_dR_eq_count_mul_hR
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:36.075772+00:00
-- url     : https://prove2.me/submissions/6fb9706e-db37-4655-aff1-931da56591bd

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
    qParent * dR a x y = (y : ℝ) * hR a h x y := by
  by_cases hne : x + y = 0
  · have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst x
    subst y
    norm_num [dR, hR, hq, N]
  · have hD := D_ne_zero ha hne
    rw [hq]
    simp only [dR, hR, if_neg hne]
    field_simp [hD]
end FD1D.LocalHazard
