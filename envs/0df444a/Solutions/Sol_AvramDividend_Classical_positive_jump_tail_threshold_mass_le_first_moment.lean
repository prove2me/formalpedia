-- Prove2me | solution 1 for AvramDividend.Classical.positive_jump_tail_threshold_mass_le_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:13:02.09569+00:00
-- url     : https://prove2.me/submissions/4e76846f-644a-41f3-8a32-0aed7f0d6a70

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive jump tails obey Markov's first-moment inequality. -/
theorem solution
    (μ : Measure ℝ≥0) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * μ {z : ℝ≥0 | t < (z : ℝ)} ≤
      ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ := by
  have hf : Measurable (fun z : ℝ≥0 => ENNReal.ofReal (z : ℝ)) := by
    fun_prop
  have hmarkov :=
    MeasureTheory.mul_meas_ge_le_lintegral
      (μ := μ) hf (ENNReal.ofReal t)
  have hsubset :
      {z : ℝ≥0 | t < (z : ℝ)} ⊆
        {z : ℝ≥0 | ENNReal.ofReal t ≤ ENNReal.ofReal (z : ℝ)} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal hz.le
  have hmono :
      μ {z : ℝ≥0 | t < (z : ℝ)} ≤
        μ {z : ℝ≥0 | ENNReal.ofReal t ≤ ENNReal.ofReal (z : ℝ)} :=
    measure_mono hsubset
  have hmul := mul_le_mul_left hmono (ENNReal.ofReal t)
  calc
    _ = μ {z : ℝ≥0 | t < (z : ℝ)} * ENNReal.ofReal t := mul_comm _ _
    _ ≤ μ {z : ℝ≥0 | ENNReal.ofReal t ≤ ENNReal.ofReal (z : ℝ)} *
          ENNReal.ofReal t := hmul
    _ = ENNReal.ofReal t * μ {z : ℝ≥0 | ENNReal.ofReal t ≤ ENNReal.ofReal (z : ℝ)} := mul_comm _ _
    _ ≤ _ := hmarkov
