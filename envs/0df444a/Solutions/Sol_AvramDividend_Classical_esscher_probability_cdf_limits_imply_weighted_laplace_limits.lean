-- Prove2me | solution 1 for AvramDividend.Classical.esscher_probability_cdf_limits_imply_weighted_laplace_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:24:55.259139+00:00
-- url     : https://prove2.me/submissions/92b2e3f6-8630-43d9-978b-d5ab42b28a2b

import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_cdf_exp_weighted_integral_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal

/-- Pointwise ENNReal probability CDF convergence gives exponential capital-transform convergence. -/
theorem solution
    (μ : ℕ → Measure ℝ) (ν : Measure ℝ)
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    [IsProbabilityMeasure ν]
    (hCDF : ∀ x : ℝ,
      Tendsto (fun n : ℕ => μ n (Iic x)) atTop (nhds (ν (Iic x))))
    (β : ℝ) (hβ : 0 < β) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (0 : ℝ),
      Real.exp (-β * x) * cdf (μ n) x ∂volume)
      atTop (nhds (∫ x in Ioi (0 : ℝ),
        Real.exp (-β * x) * cdf ν x ∂volume)) := by
  have hm (n : ℕ) :
      Measurable (fun x : ℝ => cdf (μ n) x) :=
    (monotone_cdf (μ := μ n)).measurable
  have hb (n : ℕ) (x : ℝ) :
      0 ≤ cdf (μ n) x ∧ cdf (μ n) x ≤ 1 := by
    letI : IsProbabilityMeasure (μ n) := hμ n
    exact ⟨cdf_nonneg (μ := μ n) x, cdf_le_one (μ := μ n) x⟩
  have hpt (x : ℝ) :
      Tendsto (fun n : ℕ => cdf (μ n) x)
        atTop (nhds (cdf ν x)) := by
    have hfin (n : ℕ) : μ n (Iic x) ≠ ⊤ := by
      letI : IsProbabilityMeasure (μ n) := hμ n
      exact measure_ne_top (μ n) (Iic x)
    have hνfin : ν (Iic x) ≠ ⊤ := measure_ne_top ν (Iic x)
    have ht := (ENNReal.tendsto_toReal_iff hfin hνfin).2 (hCDF x)
    have hc (n : ℕ) :
        cdf (μ n) x = (μ n (Iic x)).toReal := by
      letI : IsProbabilityMeasure (μ n) := hμ n
      exact cdf_eq_real (μ := μ n) x
    have hcv : cdf ν x = (ν (Iic x)).toReal :=
      cdf_eq_real (μ := ν) x
    simpa only [hc, hcv] using ht
  exact esscher_bounded_cdf_exp_weighted_integral_tendsto
    β hβ (fun n x => cdf (μ n) x) (fun x => cdf ν x)
    hm hb hpt
