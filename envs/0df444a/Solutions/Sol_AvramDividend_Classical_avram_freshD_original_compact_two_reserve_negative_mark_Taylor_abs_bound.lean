-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_compact_two_reserve_negative_mark_Taylor_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T14:33:50.459333+00:00
-- url     : https://prove2.me/submissions/5808094d-719f-4a6e-95cc-1520c918c951

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_topcap_compact_negative_mark_loss_abs_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ t < 0, w t = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C})
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {t : ℝ | 0 < t ∧ ENNReal.ofReal t < C}) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ u ∈ Icc a b, ∀ y ∈ Icc a b, ∀ z : ℝ, z < 0 →
        |(w (u + z) - w u -
            (if -1 < z then z * deriv w u else 0)) -
          (w (y + z) - w y -
            (if -1 < z then z * deriv w y else 0))| ≤ L := by
  obtain ⟨K, hK, hKV⟩ :=
    avram_bvb_topcap_compact_negative_mark_loss_abs_bound
      w hw_cont hw_neg b (ha.trans hab)
  obtain ⟨M, hM, hMV⟩ :=
    avram_p4_d_dividend_ubv_compact_interior_derivative_bound
      C w hw_smooth a b hab hBand
  refine ⟨2 * (K + M), by positivity, ?_⟩
  intro u hu y hy z hz
  have hzu : |w (u + z) - w u| ≤ K :=
    hKV u z (ha.trans hu.1) hu.2 hz
  have hzy : |w (y + z) - w y| ≤ K :=
    hKV y z (ha.trans hy.1) hy.2 hz
  have hsmall (r : ℝ) (hr : r ∈ Icc a b) :
      |if -1 < z then z * deriv w r else 0| ≤ M := by
    split_ifs with hz1
    · have hzabs : |z| ≤ 1 := by
        rw [abs_of_neg hz]
        linarith
      calc
        |z * deriv w r| = |z| * |deriv w r| := abs_mul _ _
        _ ≤ 1 * |deriv w r| :=
          mul_le_mul_of_nonneg_right hzabs (abs_nonneg _)
        _ = |deriv w r| := one_mul _
        _ ≤ M := hMV r hr
    · simpa only [abs_zero] using hM
  have hku :
      |(w (u + z) - w u) -
        (if -1 < z then z * deriv w u else 0)| ≤ K + M := by
    calc
      _ ≤ |w (u + z) - w u| +
          |if -1 < z then z * deriv w u else 0| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le (w (u + z) - w u)
                (-(if -1 < z then z * deriv w u else 0)))
      _ ≤ K + M := add_le_add hzu (hsmall u hu)
  have hky :
      |(w (y + z) - w y) -
        (if -1 < z then z * deriv w y else 0)| ≤ K + M := by
    calc
      _ ≤ |w (y + z) - w y| +
          |if -1 < z then z * deriv w y else 0| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le (w (y + z) - w y)
                (-(if -1 < z then z * deriv w y else 0)))
      _ ≤ K + M := add_le_add hzy (hsmall y hy)
  calc
    _ ≤ |w (u + z) - w u -
            (if -1 < z then z * deriv w u else 0)| +
          |w (y + z) - w y -
            (if -1 < z then z * deriv w y else 0)| := by
              simpa only [sub_eq_add_neg, abs_neg] using
                (abs_add_le
                  (w (u + z) - w u -
                    (if -1 < z then z * deriv w u else 0))
                  (-(w (y + z) - w y -
                    (if -1 < z then z * deriv w y else 0))))
    _ ≤ (K + M) + (K + M) := add_le_add hku hky
    _ = 2 * (K + M) := by ring
