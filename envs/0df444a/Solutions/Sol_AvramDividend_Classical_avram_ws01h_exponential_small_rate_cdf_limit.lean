-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_exponential_small_rate_cdf_limit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:34:58.214181+00:00
-- url     : https://prove2.me/submissions/baacf333-fcfc-4b76-840c-c38ac127bc9a

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open AvramDividend.Classical MeasureTheory Filter
open scoped ENNReal Topology
theorem solution
    (b : ℝ) (lam : ℝ → ℝ) (l : Filter ℝ)
    (hlam : Tendsto lam l (𝓝 (0 : ℝ))) :
    Tendsto (fun p : ℝ =>
      ENNReal.ofReal (1 - Real.exp (-(lam p * b))))
      l (𝓝 (0 : ℝ≥0∞)) := by
  have h1 : Tendsto (fun p => 1 - Real.exp (-(lam p * b))) l (𝓝 (1 - Real.exp (-((0:ℝ) * b)))) := by
    refine tendsto_const_nhds.sub (Real.continuous_exp.continuousAt.tendsto.comp ?_)
    exact ((hlam.mul_const b).neg)
  have h2 := (ENNReal.continuous_ofReal.tendsto _).comp h1
  simp only [zero_mul, neg_zero, Real.exp_zero, sub_self, ENNReal.ofReal_zero] at h2
  exact h2
