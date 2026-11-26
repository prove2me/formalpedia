-- Prove2me | solution 1 for FD1D.LocalHazard.abs_w_le_V_add_half_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:00:31.271661+00:00
-- url     : https://prove2.me/submissions/70f1be0b-1bf6-4fe4-bf47-c51de4233620

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Hazard
import Theorems.Thm_FD1D_LocalHazard_V_nonneg
import Theorems.Thm_FD1D_LocalHazard_w_sq_eq
import Theorems.Thm_FD1D_LocalHazard_N_div_N_add_two_mul_a_le_one
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open FD1D.LocalHazard
namespace FD1D.LocalHazard
theorem _root_.solution {a h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 ≤ h) :
    |w a h x y| ≤ V a h x y + h / 2 := by
  have hV : 0 ≤ V a h x y := V_nonneg ha hh
  have hsum : 0 ≤ h + V a h x y := add_nonneg hh hV
  have hprod : 0 ≤ V a h x y * (h + V a h x y) :=
    mul_nonneg hV hsum
  have hratio := N_div_N_add_two_mul_a_le_one ha x y
  have hwsq : w a h x y ^ 2 ≤ V a h x y * (h + V a h x y) := by
    rw [w_sq_eq ha]
    calc
      N x y / (N x y + 2 * a) * V a h x y * (h + V a h x y) =
          (N x y / (N x y + 2 * a)) *
            (V a h x y * (h + V a h x y)) := by ring
      _ ≤ 1 * (V a h x y * (h + V a h x y)) :=
        mul_le_mul_of_nonneg_right hratio hprod
      _ = V a h x y * (h + V a h x y) := one_mul _
  have htarget : 0 ≤ V a h x y + h / 2 := by positivity
  have htargetSq :
      w a h x y ^ 2 ≤ (V a h x y + h / 2) ^ 2 := by
    nlinarith [sq_nonneg h]
  have habsSq :
      |w a h x y| ^ 2 ≤ (V a h x y + h / 2) ^ 2 := by
    simpa using htargetSq
  nlinarith [abs_nonneg (w a h x y)]
end FD1D.LocalHazard
