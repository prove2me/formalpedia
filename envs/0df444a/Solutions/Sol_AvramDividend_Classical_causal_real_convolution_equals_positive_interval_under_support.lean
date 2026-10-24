-- Prove2me | solution 1 for AvramDividend.Classical.causal_real_convolution_equals_positive_interval_under_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:18:02.823245+00:00
-- url     : https://prove2.me/submissions/be041591-155a-4ab6-a387-de907629e4e4

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A real convolution of causal kernels integrates only over the positive
time interval, with no additional integrability hypotheses. -/
theorem solution
    (f g : ℝ → ℝ)
    (hfzero : ∀ y : ℝ, y ≤ 0 → f y = 0)
    (hgzero : ∀ y : ℝ, y ≤ 0 → g y = 0)
    (x : ℝ) :
    (∫ y : ℝ, f y * g (x - y) ∂volume) =
      ∫ y in Ioc (0 : ℝ) x, f y * g (x - y) ∂volume := by
  calc
    (∫ y : ℝ, f y * g (x - y) ∂volume) =
        ∫ y : ℝ, (Ioc (0 : ℝ) x).indicator
          (fun t : ℝ => f t * g (x - t)) y ∂volume := by
          congr 1
          funext y
          by_cases hy : y ∈ Ioc (0 : ℝ) x
          · simp only [Set.indicator_of_mem hy]
          · have hor : y ≤ 0 ∨ x < y := by
              simpa only [Set.mem_Ioc, not_and_or, not_lt, not_le] using hy
            simp only [Set.indicator_of_notMem hy]
            rcases hor with hnonpos | hlarge
            · rw [hfzero y hnonpos, zero_mul]
            · have hother : x - y ≤ 0 := sub_nonpos.mpr (le_of_lt hlarge)
              rw [hgzero (x - y) hother, mul_zero]
    _ = ∫ y in Ioc (0 : ℝ) x, f y * g (x - y) ∂volume :=
      integral_indicator measurableSet_Ioc
