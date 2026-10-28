-- Prove2me | solution 1 for AvramDividend.Classical.esscher_true_exp_rate_cdf_abel_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T17:51:24.032916+00:00
-- url     : https://prove2.me/submissions/b3179a91-1d8c-4630-9d4f-31f0ac489731

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE
import Theorems.Thm_AvramDividend_Classical_esscher_exp_clock_rate_scaling_true_law
import Theorems.Thm_AvramDividend_Classical_esscher_exp_clock_cdf_abel_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set

/-- The actual exponentially distributed random horizons of vanishing rate
    sample the limiting value of a bounded finite-horizon CDF. -/
theorem solution
    (f : ℝ → ℝ) (L : ℝ)
    (hf : Tendsto f atTop (nhds L))
    (hmeas : Measurable f) (hbound : ∀ t, ‖f t‖ ≤ (1 : ℝ))
    (p : ℕ → ℝ)
    (hp : Tendsto p atTop (nhdsWithin (0 : ℝ) (Ioi 0)))
    (hpos : ∀ n, 0 < p n) :
    Tendsto (fun n => ∫ t, f t ∂expMeasure (p n))
      atTop (nhds L) := by
  letI : IsProbabilityMeasure (expMeasure (1 : ℝ)) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  have hzero : expMeasure (1 : ℝ) (Iic (0 : ℝ)) = 0 := by
    calc
      expMeasure (1 : ℝ) (Iic (0 : ℝ)) =
          ENNReal.ofReal (cdf (expMeasure (1 : ℝ)) 0) :=
        (ofReal_cdf (expMeasure (1 : ℝ)) 0).symm
      _ = 0 := by
        rw [cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1) 0]
        norm_num
  have hbad : {t : ℝ | ¬(0 : ℝ) < t} = Iic (0 : ℝ) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Iic, not_lt]
  have hE : ∀ᵐ t ∂expMeasure (1 : ℝ), (0 : ℝ) < t := by
    rw [ae_iff, hbad]
    exact hzero
  have hmeasAE (n : ℕ) :
      AEStronglyMeasurable (fun t : ℝ => f (t / p n))
        (expMeasure (1 : ℝ)) :=
    (hmeas.comp (measurable_id.div_const _)).aestronglyMeasurable
  have hboundAE (n : ℕ) :
      ∀ᵐ t ∂expMeasure (1 : ℝ), ‖f (t / p n)‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall (fun t => hbound (t / p n))
  have hlim :=
    esscher_exp_clock_cdf_abel_limit
      (expMeasure (1 : ℝ)) (fun t : ℝ => t) hE
      f L hf p hp hmeasAE hboundAE
  have heq (n : ℕ) :
      (∫ t, f t ∂expMeasure (p n)) =
        ∫ t, f (t / p n) ∂expMeasure (1 : ℝ) := by
    rw [← esscher_exp_clock_rate_scaling_true_law (p n) (hpos n)]
    exact integral_map_of_stronglyMeasurable
      (measurable_id.div_const (p n)) hmeas.stronglyMeasurable
  have hfun :
      (fun n => ∫ t, f t ∂expMeasure (p n)) =
      (fun n => ∫ t, f (t / p n) ∂expMeasure (1 : ℝ)) := by
    funext n
    exact heq n
  rw [hfun]
  exact hlim
