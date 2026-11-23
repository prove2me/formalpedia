-- Prove2me | solution 1 for ExactDFTRefine.Main.eq_8_9
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:10:38.646845+00:00
-- url     : https://prove2.me/submissions/3b84ce91-bea6-4a82-ada2-e61f9baebec6

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments
import Theorems.Thm_ExactDFTRefine_Main_proposition_3_2
import Theorems.Thm_ExactDFTRefine_Main_appendix_a

open ExactDFTRefine.Main

set_option maxRecDepth 100000

theorem solution :
    ((145 : ℝ) / 20) ^ Cpar ≤ Ebound ∧
    (20 : ℝ) ^ Cpar * moment tpar targetsT =
      145 / ((145 : ℝ) / 20) ^ Cpar * (moment tpar targetsT / (145 : ℝ) ^ tpar) ∧
    (20 : ℝ) ^ Cpar * moment tpar targetsT ≥ 145 * Lbound / Ebound := by
  obtain ⟨hP, hT, hratio⟩ := proposition_3_2
  let ell : ℝ := 1981001468867 / 10 ^ 12
  have hC0 : 0 ≤ Cpar := by norm_num [Cpar]
  have hell0 : 0 ≤ ell := by norm_num [ell]
  have hcert : (145 : ℝ) / 20 ≤ SN 20 ell := by
    norm_num [SN, ell, Finset.sum_range_succ, Nat.factorial]
  have hSN : SN 20 ell ≤ Real.exp ell := by
    exact Real.sum_le_exp_of_nonneg hell0 20
  have hlog : Real.log ((145 : ℝ) / 20) ≤ ell := by
    exact (Real.log_le_iff_le_exp (by norm_num)).2 (hcert.trans hSN)
  have hx0 : 0 ≤ Cpar * ell := mul_nonneg hC0 hell0
  have hx1 : Cpar * ell ≤ 1 := by norm_num [Cpar, ell]
  have h8 : ((145 : ℝ) / 20) ^ Cpar ≤ Ebound := by
    calc
      ((145 : ℝ) / 20) ^ Cpar = Real.exp (Real.log ((145 : ℝ) / 20) * Cpar) :=
        Real.rpow_def_of_pos (by norm_num) Cpar
      _ ≤ Real.exp (ell * Cpar) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hlog hC0)
      _ = Real.exp (Cpar * ell) := by ring_nf
      _ ≤ UN 6 (Cpar * ell) := (appendix_a 6 (by norm_num) (Cpar * ell) hx0 hx1).2
      _ ≤ Ebound := by
        norm_num [UN, SN, ell, Cpar, Ebound, Finset.sum_range_succ, Nat.factorial]
  have hnorm : (20 : ℝ) ^ Cpar * (145 : ℝ) ^ tpar =
      145 / ((145 : ℝ) / 20) ^ Cpar := by
    rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 145) (by norm_num : (0 : ℝ) ≤ 20)]
    rw [tpar, Real.rpow_sub (by norm_num : (0 : ℝ) < 145), Real.rpow_one]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 20) Cpar),
      ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 145) Cpar)]
  have hpow145 : (145 : ℝ) ^ tpar ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (by norm_num) tpar)
  have hid : (20 : ℝ) ^ Cpar * moment tpar targetsT =
      145 / ((145 : ℝ) / 20) ^ Cpar * (moment tpar targetsT / (145 : ℝ) ^ tpar) := by
    calc
      (20 : ℝ) ^ Cpar * moment tpar targetsT =
          ((20 : ℝ) ^ Cpar * (145 : ℝ) ^ tpar) *
            (moment tpar targetsT / (145 : ℝ) ^ tpar) := by
        field_simp [hpow145]
      _ = _ := by rw [hnorm]
  have hE0 : 0 < Ebound := by norm_num [Ebound]
  have haC0 : 0 < ((145 : ℝ) / 20) ^ Cpar := Real.rpow_pos_of_pos (by norm_num) Cpar
  have hK : 145 / Ebound ≤ 145 / ((145 : ℝ) / 20) ^ Cpar := by
    exact (div_le_div_iff₀ hE0 haC0).2 (by nlinarith)
  have hmoment0 : 0 ≤ moment tpar targetsT / (145 : ℝ) ^ tpar :=
    le_trans (by norm_num [Lbound]) hT
  refine ⟨h8, hid, ?_⟩
  calc
    (20 : ℝ) ^ Cpar * moment tpar targetsT =
        145 / ((145 : ℝ) / 20) ^ Cpar * (moment tpar targetsT / (145 : ℝ) ^ tpar) := hid
    _ ≥ (145 / Ebound) * (moment tpar targetsT / (145 : ℝ) ^ tpar) :=
      mul_le_mul_of_nonneg_right hK hmoment0
    _ ≥ (145 / Ebound) * Lbound :=
      mul_le_mul_of_nonneg_left hT (by exact div_nonneg (by norm_num) hE0.le)
    _ = 145 * Lbound / Ebound := by ring
