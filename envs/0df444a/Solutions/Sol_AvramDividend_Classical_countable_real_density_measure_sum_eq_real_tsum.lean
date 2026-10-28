-- Prove2me | solution 1 for AvramDividend.Classical.countable_real_density_measure_sum_eq_real_tsum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:30:49.391988+00:00
-- url     : https://prove2.me/submissions/38ecfe39-2f53-432d-9233-fd834c2075c6

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_AvramDividend_Classical_countable_real_density_measure_sum_eq_withDensity_tsum
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    (F : ℕ → ℝ → ℝ) (m : ℕ → Measure ℝ)
    (hFmeas : ∀ n : ℕ, Measurable (F n))
    (hFpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hFsummable : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hm : ∀ n : ℕ, m n =
      volume.withDensity (fun x : ℝ => ENNReal.ofReal (F n x))) :
    Measure.sum m =
      volume.withDensity (fun x : ℝ =>
        ENNReal.ofReal (∑' n : ℕ, F n x)) := by
  have e : (fun x : ℝ => ENNReal.ofReal (∑' n : ℕ, F n x)) =
      ∑' n : ℕ, (fun x : ℝ => ENNReal.ofReal (F n x)) := by
    funext x
    rw [ENNReal.tsum_apply, ENNReal.ofReal_tsum_of_nonneg (fun n => hFpos n x) (hFsummable x)]
  rw [e, withDensity_tsum (fun n => (hFmeas n).ennreal_ofReal)]
  exact congrArg Measure.sum (funext hm)
