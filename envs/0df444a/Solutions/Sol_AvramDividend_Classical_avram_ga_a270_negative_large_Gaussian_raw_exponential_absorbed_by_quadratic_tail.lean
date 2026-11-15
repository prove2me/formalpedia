-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a270_negative_large_Gaussian_raw_exponential_absorbed_by_quadratic_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:05:45.08921+00:00
-- url     : https://prove2.me/submissions/1ebac2db-c11a-4658-8ac8-faf59a47feb3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (theta delta r : ℝ) (hθ : 0 ≤ theta) (hδ : 0 < delta)
    (hLarge : delta ≤ |r|) :
    Real.exp (theta*r) ≤
      (if delta ≤ r then Real.exp (theta*r) else r^2/delta^2) := by
  by_cases hp : delta ≤ r
  · simp only [if_pos hp,le_refl]
  · simp only [if_neg hp]
    have hNeg : r ≤ -delta := by
      rcases le_total 0 r with h0 | h0
      · rw [abs_of_nonneg h0] at hLarge
        linarith
      · rw [abs_of_nonpos h0] at hLarge
        linarith
    have hExp : Real.exp (theta*r) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hθ
        (le_trans hNeg (neg_nonpos.mpr hδ.le)))
    have hδ2 : 0 < delta^2 := sq_pos_of_pos hδ
    have hSquare : delta^2 ≤ r^2 := by
      have h := mul_nonneg
        (sub_nonneg.mpr (by linarith : delta ≤ -r))
        (add_nonneg (by linarith : 0 ≤ -r) hδ.le)
      nlinarith
    have hDiv : 1 ≤ r^2/delta^2 :=
      (le_div_iff₀ hδ2).2 (by nlinarith)
    linarith
