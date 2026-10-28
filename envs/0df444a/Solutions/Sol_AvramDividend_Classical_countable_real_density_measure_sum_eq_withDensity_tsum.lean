-- Prove2me | solution 1 for AvramDividend.Classical.countable_real_density_measure_sum_eq_withDensity_tsum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:22:24.14599+00:00
-- url     : https://prove2.me/submissions/cdead5fd-99b6-4ce5-b951-35cee11ae35d

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic.FunProp
open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hm : ∀ n : ℕ, m n =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum m =
      volume.withDensity
        (∑' n : ℕ, (fun x : ℝ => ENNReal.ofReal (F n x))) := by
  rw [withDensity_tsum (fun n => (hFmeas n).ennreal_ofReal)]
  exact congrArg Measure.sum (funext hm)
