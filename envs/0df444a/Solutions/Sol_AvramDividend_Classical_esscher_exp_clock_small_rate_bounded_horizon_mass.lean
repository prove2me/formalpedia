-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exp_clock_small_rate_bounded_horizon_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:49:04.739615+00:00
-- url     : https://prove2.me/submissions/5406ac46-a20f-4bb2-b041-588a72cfe783

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal

/-- A genuine exponential clock of vanishing rate escapes every bounded horizon. -/
theorem solution
    (p : ℕ → ℝ) (hp : Tendsto p atTop (nhds (0 : ℝ)))
    (hpos : ∀ n, 0 < p n)
    (T : ℝ) (hT : 0 ≤ T) :
    Tendsto (fun n => expMeasure (p n) (Iic T))
      atTop (nhds (0 : ℝ≥0∞)) := by
  have hform (n : ℕ) :
      expMeasure (p n) (Iic T) =
        ENNReal.ofReal (1 - Real.exp (-(p n * T))) := by
    letI : IsProbabilityMeasure (expMeasure (p n)) :=
      isProbabilityMeasure_expMeasure (hpos n)
    calc
      expMeasure (p n) (Iic T) =
          ENNReal.ofReal (cdf (expMeasure (p n)) T) :=
        (ofReal_cdf (expMeasure (p n)) T).symm
      _ = ENNReal.ofReal (1 - Real.exp (-(p n * T))) := by
        rw [cdf_expMeasure_eq (hpos n) T, if_pos hT]
  have hcont : Continuous
      (fun r : ℝ => 1 - Real.exp (-(r * T))) :=
    continuous_const.sub
      (Real.continuous_exp.comp (continuous_id.mul continuous_const).neg)
  have hreal :
      Tendsto (fun n => (1 : ℝ) - Real.exp (-(p n * T)))
        atTop (nhds (0 : ℝ)) := by
    have h := (hcont.tendsto (0 : ℝ)).comp hp
    have heq : (1 : ℝ) - Real.exp (-((0 : ℝ) * T)) = 0 := by norm_num
    rw [heq] at h
    exact h
  have hnonneg :
      Tendsto (fun n => ENNReal.ofReal (1 - Real.exp (-(p n * T))))
        atTop (nhds (0 : ℝ≥0∞)) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    change Tendsto
      (fun n : ℕ => ENNReal.ofReal (1 - Real.exp (-(p n * T))))
      atTop (nhds (ENNReal.ofReal (0 : ℝ))) at h
    simpa only [ENNReal.ofReal_zero] using h
  simpa only [hform] using hnonneg
