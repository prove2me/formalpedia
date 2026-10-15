-- Prove2me | solution 1 for FakeAccounts.Platform.uninformed_jensen
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-14T12:45:26.278468+00:00
-- url     : https://prove2.me/submissions/ecc99542-7a4e-49b6-ab9e-d4aa69d5dae8

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting
open FakeAccounts.Platform

theorem solution(P : Params) (hP : Standing P) :
    ∀ d, 0 < cost P d →
      P.rho * nUn P P.qH d + (1 - P.rho) * nUn P P.qL d < nUn P (meanQ P) d := by
  intro d hc
  have hl1 := hP.l_lt_one
  have hρ := hP.rho_pos
  have hρ1 := hP.rho_lt_one
  have hqL := hP.qL_pos
  have hqLH := hP.qL_lt_qH
  have hqH : 0 < P.qH := by linarith
  have hE : 0 < meanQ P := by
    unfold meanQ
    nlinarith [mul_pos hρ hqH, mul_pos (sub_pos.mpr hρ1) hqL]
  have key : 1 / meanQ P < P.rho / P.qH + (1 - P.rho) / P.qL := by
    rw [div_add_div _ _ hqH.ne' hqL.ne', div_lt_div_iff₀ hE (mul_pos hqH hqL)]
    unfold meanQ
    nlinarith [mul_pos (mul_pos hρ (sub_pos.mpr hρ1)) (pow_pos (sub_pos.mpr hqLH) 2)]
  unfold nUn
  have e1 : P.rho * ((1 - P.l) * (1 - cost P d / P.qH)) + (1 - P.rho) * ((1 - P.l) * (1 - cost P d / P.qL)) = (1 - P.l) * (1 - cost P d * (P.rho / P.qH + (1 - P.rho) / P.qL)) := by
    ring
  rw [e1]
  apply mul_lt_mul_of_pos_left _ (by linarith)
  have h2 := mul_lt_mul_of_pos_left key hc
  rw [mul_one_div] at h2
  linarith
