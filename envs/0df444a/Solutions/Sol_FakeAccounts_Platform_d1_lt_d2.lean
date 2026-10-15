-- Prove2me | solution 1 for FakeAccounts.Platform.d1_lt_d2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:43:48.810575+00:00
-- url     : https://prove2.me/submissions/34cd84ab-c32f-42e1-9be0-a408b6948ef3

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting
open FakeAccounts.Platform

theorem solution(P : Params) (hP : Standing P) : d1 P < d2 P := by
  have hτ : 0 < 1 - P.tau := by linarith [hP.tau_lt_one]
  have hl := hP.l_pos
  have hl1 := hP.l_lt_one
  have hρ := hP.rho_pos
  have hρ1 := hP.rho_lt_one
  have hqL := hP.qL_pos
  have hqLH := hP.qL_lt_qH
  have hqH : 0 < P.qH := by linarith
  have hE : 0 < meanQ P := by
    unfold meanQ
    nlinarith [mul_pos hρ hqH, mul_pos (sub_pos.mpr hρ1) hqL]
  have hA : 0 < P.lamI * P.mu * (1 - P.l) := mul_pos (mul_pos hP.lamI_pos hP.mu_pos) (by linarith)
  have hterm : P.qH * (meanQ P - P.qL) / (P.l * meanQ P * (P.qH - P.qL)) = P.rho * P.qH / (P.l * meanQ P) := by
    have h1 : P.qH - P.qL ≠ 0 := (sub_pos.mpr hqLH).ne'
    rw [div_eq_div_iff (mul_ne_zero (mul_ne_zero hl.ne' hE.ne') h1) (mul_ne_zero hl.ne' hE.ne')]
    unfold meanQ
    ring
  have h1 : P.rho * P.qH / (P.l * meanQ P) < 1 / P.l := by
    rw [div_lt_div_iff₀ (mul_pos hl hE) hl]
    unfold meanQ
    nlinarith [mul_pos hl (mul_pos (sub_pos.mpr hρ1) hqL)]
  have heta : eta1 P < eta2 P := by
    unfold eta1 eta2
    rw [hterm]
    have e2 : 1 / P.l * P.lamI * P.mu * (1 - P.l ^ 2) = P.lamI * P.mu * (1 - P.l) * (1 / P.l + 1) := by
      field_simp
      ring
    rw [e2]
    apply mul_lt_mul_of_pos_left _ hA
    linarith
  unfold d1 d2
  apply mul_lt_mul_of_pos_left _ hτ
  linarith
