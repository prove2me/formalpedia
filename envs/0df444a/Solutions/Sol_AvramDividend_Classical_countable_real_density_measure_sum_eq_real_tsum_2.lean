-- Prove2me | solution 2 for AvramDividend.Classical.countable_real_density_measure_sum_eq_real_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:30:53.126985+00:00
-- url     : https://prove2.me/submissions/f833edf9-9393-4b68-a986-7c31b5492086

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_withDensity_tsum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Identify a summable positive real renewal density series with the density
of the countable sum of its associated finite positive measures. -/
theorem solution (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFsummable : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hm : ∀ n : ℕ, m n =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum m =
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (∑' n : ℕ, F n x)) := by
  calc
    Measure.sum m =
        volume.withDensity
          (∑' n : ℕ, (fun x : ℝ => ENNReal.ofReal (F n x))) :=
      countable_real_density_measure_sum_eq_withDensity_tsum F m hFmeas hm
    _ = volume.withDensity
          (fun x : ℝ => ENNReal.ofReal (∑' n : ℕ, F n x)) := by
      congr 1
      funext x
      simpa only [ENNReal.tsum_apply] using
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n : ℕ => hFpos n x) (hFsummable x)).symm
