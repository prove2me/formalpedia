-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger148_weighted_clipped_discount_euler_boundary_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:11:05.202112+00:00
-- url     : https://prove2.me/submissions/82191986-ef43-4e90-bc38-2e56ba4c6d64

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_gledger147_clipped_final_discount_cell_absolute_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
theorem solution
    (q t r δ a K : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hrδ : r ≤ δ) (hK : 0 ≤ K) (ha : |a| ≤ K) :
    |(Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))) * a| ≤ 2 * q * δ * K := by
  have hδ : 0 ≤ δ := le_trans hr hrδ
  have hqd : 0 ≤ q * δ := mul_nonneg hq hδ
  have ht1 : Real.exp (-(q * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq ht))
  have ht0 : 0 ≤ Real.exp (-(q * t)) := (Real.exp_pos _).le
  have hqterm : |q * δ * Real.exp (-(q * t))| ≤ q * δ := by
    rw [abs_of_nonneg (mul_nonneg hqd ht0)]
    nlinarith [mul_nonneg hqd (sub_nonneg.mpr ht1)]
  have hcross :=
    AvramDividend.Classical.avram_gledger147_clipped_final_discount_cell_absolute_bound
      q t r δ hq ht hr hrδ
  have hcell :
      |Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
        q * δ * Real.exp (-(q * t))| ≤ q * δ + q * δ := by
    calc
      _ ≤ |Real.exp (-(q * (t + r))) - Real.exp (-(q * t))| +
            |q * δ * Real.exp (-(q * t))| := abs_add_le _ _
      _ ≤ q * δ + q * δ := add_le_add hcross hqterm
  rw [abs_mul]
  calc
    _ ≤ (q * δ + q * δ) * |a| :=
      mul_le_mul_of_nonneg_right hcell (abs_nonneg _)
    _ ≤ (q * δ + q * δ) * K :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = 2 * q * δ * K := by ring
