-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger147_clipped_final_discount_cell_absolute_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:04:52.927227+00:00
-- url     : https://prove2.me/submissions/6893868e-36c2-4e0b-ab04-489e4ca23342

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
theorem solution
    (q t r δ : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hrδ : r ≤ δ) :
    |Real.exp (-(q * (t + r))) - Real.exp (-(q * t))| ≤ q * δ := by
  have hqr : 0 ≤ q * r := mul_nonneg hq hr
  have hqt : 0 ≤ q * t := mul_nonneg hq ht
  have ht1 : Real.exp (-(q * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqt)
  have hr1 : Real.exp (-(q * r)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqr)
  have hpos : 0 ≤ Real.exp (-(q * t)) := (Real.exp_pos _).le
  have hexp : Real.exp (-(q * (t + r))) =
      Real.exp (-(q * t)) * Real.exp (-(q * r)) := by
    calc
      Real.exp (-(q * (t + r))) =
        Real.exp (-(q * t) + -(q * r)) := by congr 1; ring
      _ = _ := Real.exp_add _ _
  have hdiff : Real.exp (-(q * (t + r))) ≤ Real.exp (-(q * t)) := by
    rw [hexp]
    nlinarith [mul_nonneg hpos (sub_nonneg.mpr hr1)]
  have hrem : 1 - Real.exp (-(q * r)) ≤ q * r := by
    have h := Real.add_one_le_exp (-(q * r))
    linarith
  calc
    |Real.exp (-(q * (t + r))) - Real.exp (-(q * t))| =
        Real.exp (-(q * t)) - Real.exp (-(q * (t + r))) := by
          rw [abs_of_nonpos (sub_nonpos.mpr hdiff)]
          ring
    _ = Real.exp (-(q * t)) * (1 - Real.exp (-(q * r))) := by
      rw [hexp]
      ring
    _ ≤ 1 * (1 - Real.exp (-(q * r))) :=
      mul_le_mul_of_nonneg_right ht1 (sub_nonneg.mpr hr1)
    _ ≤ q * r := by simpa only [one_mul] using hrem
    _ ≤ q * δ := mul_le_mul_of_nonneg_left hrδ hq
