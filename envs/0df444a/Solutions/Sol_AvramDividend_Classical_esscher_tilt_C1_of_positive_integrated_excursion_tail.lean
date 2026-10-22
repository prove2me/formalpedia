-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilt_C1_of_positive_integrated_excursion_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T23:26:10.655858+00:00
-- url     : https://prove2.me/submissions/e7dc820c-a205-4baa-82cf-60905c195ce4

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_positive_integrated_excursion_tail
import Theorems.Thm_AvramDividend_Classical_esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set MeasureTheory intervalIntegral

theorem solution (T W V : ℝ → ℝ) (a c φ : ℝ) (ha : 0 < a)
    (hT : ContinuousOn T (Ioi (0 : ℝ)))
    (hW : ∀ x : ℝ, 0 < x →
      W x = c * Real.exp (∫ t in a..x, T t))
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  have hWc1 : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) :=
    contDiffOn_one_of_positive_integrated_excursion_tail T W a c ha hT hW
  exact esscher_tilt_contDiffOn_one_of_scale_contDiffOn_one φ W V hWc1 hV
