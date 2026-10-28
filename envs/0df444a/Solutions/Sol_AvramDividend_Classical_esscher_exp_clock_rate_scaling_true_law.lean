-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exp_clock_rate_scaling_true_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:45:59.756311+00:00
-- url     : https://prove2.me/submissions/2e729cb3-6718-4713-94d0-6bbfd6247241

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory Set

/-- The true exponential laws obey positive reciprocal clock scaling. -/
theorem solution (p : ℝ) (hp : 0 < p) :
    Measure.map (fun t : ℝ => t / p) (expMeasure (1 : ℝ)) =
      expMeasure p := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hmap : Measurable (fun t : ℝ => t / p) :=
    measurable_id.div_const p
  have hpre (x : ℝ) :
      (fun t : ℝ => t / p) ⁻¹' Iic x = Iic (p * x) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Iic,
      div_le_iff₀ hp, mul_comm x p]
  have hCDF (x : ℝ) :
      cdf (expMeasure (1 : ℝ)) (p * x) =
        cdf (expMeasure p) x := by
    rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1),
      cdf_expMeasure_eq hp]
    by_cases hx : 0 ≤ x
    · have hpx : 0 ≤ p * x := mul_nonneg (le_of_lt hp) hx
      simp [hx, hpx]
    · have hpx : ¬ 0 ≤ p * x :=
        not_le.mpr (mul_neg_of_pos_of_neg hp (lt_of_not_ge hx))
      simp [hx, hpx]
  apply Measure.ext_of_Iic
  intro x
  calc
    (Measure.map (fun t : ℝ => t / p) (expMeasure (1 : ℝ))) (Iic x) =
        expMeasure (1 : ℝ) (Iic (p * x)) := by
      rw [Measure.map_apply hmap measurableSet_Iic, hpre]
    _ = ENNReal.ofReal (cdf (expMeasure (1 : ℝ)) (p * x)) :=
      (ofReal_cdf (expMeasure (1 : ℝ)) (p * x)).symm
    _ = ENNReal.ofReal (cdf (expMeasure p) x) := by rw [hCDF]
    _ = expMeasure p (Iic x) := ofReal_cdf (expMeasure p) x
