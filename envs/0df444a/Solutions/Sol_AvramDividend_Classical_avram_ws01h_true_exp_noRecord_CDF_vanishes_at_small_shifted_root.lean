-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_exp_noRecord_CDF_vanishes_at_small_shifted_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:21:07.83445+00:00
-- url     : https://prove2.me/submissions/79ae39b7-bf58-4c82-b938-3f0e8e9516ea

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.CDF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_exponential_small_rate_cdf_limit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical ProbabilityTheory MeasureTheory Filter Set
open scoped ENNReal Topology

/-- The actual Exp(λₚ) no-record CDF error vanishes as the shifted
Lévy-root rate tends to zero through strictly positive rates. -/
theorem solution
    (b : ℝ) (hb : 0 ≤ b) (lam : ℝ → ℝ)
    (hlampos : ∀ p : ℝ, 0 < p → 0 < lam p)
    (hlam : Tendsto lam (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ))) :
    Tendsto (fun p : ℝ => expMeasure (lam p) (Iic b))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (0 : ℝ≥0∞)) := by
  have hbound := avram_ws01h_exponential_small_rate_cdf_limit
    b lam (nhdsWithin (0 : ℝ) (Ioi 0)) hlam
  have heq :
      (fun p : ℝ => expMeasure (lam p) (Iic b)) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun p : ℝ => ENNReal.ofReal
        (1 - Real.exp (-(lam p * b)))) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hpos : 0 < lam p := hlampos p hp
    letI : IsProbabilityMeasure (expMeasure (lam p)) :=
      isProbabilityMeasure_expMeasure hpos
    rw [← ofReal_cdf, cdf_expMeasure_eq hpos, if_pos hb]
  exact hbound.congr' heq.symm
