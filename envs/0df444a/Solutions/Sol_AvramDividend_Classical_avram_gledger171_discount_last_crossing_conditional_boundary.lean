-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger171_discount_last_crossing_conditional_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:25:04.542245+00:00
-- url     : https://prove2.me/submissions/16d34bc3-23b3-4efb-aabd-35461c3e9fff

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger147_clipped_final_discount_cell_absolute_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger148_weighted_clipped_discount_euler_boundary_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
theorem solution
    (q t r δ a K : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hrδ : r ≤ δ) (hK : 0 ≤ K) (ha : |a| ≤ K)
    (b : Prop) [Decidable b] :
    |(Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
       (if b then q * δ * Real.exp (-(q * t)) else 0)) * a| ≤
      2 * q * δ * K := by
  by_cases hb : b
  · simpa only [if_pos hb] using
      avram_gledger148_weighted_clipped_discount_euler_boundary_bound
        q t r δ a K hq ht hr hrδ hK ha
  · have hdisc :=
      avram_gledger147_clipped_final_discount_cell_absolute_bound
        q t r δ hq ht hr hrδ
    have hδ : 0 ≤ δ := le_trans hr hrδ
    have hqδ : 0 ≤ q * δ := mul_nonneg hq hδ
    calc
      |(Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
          (if b then q * δ * Real.exp (-(q * t)) else 0)) * a| =
        |Real.exp (-(q * (t + r))) - Real.exp (-(q * t))| * |a| := by
          simp only [if_neg hb, add_zero, abs_mul]
      _ ≤ q * δ * K := mul_le_mul hdisc ha (abs_nonneg _) hqδ
      _ ≤ 2 * q * δ * K := by nlinarith [mul_nonneg hqδ hK]
