-- Prove2me | solution 1 for AvramDividend.Classical.excursion_capped_laplace_tendsto_of_finite_weak
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:23:39.980397+00:00
-- url     : https://prove2.me/submissions/ab93b4ab-3ff5-45a5-839d-a509c33a521b

import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Theorems.Thm_AvramDividend_Classical_excursion_capped_laplace_bounded_nnreal_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-!
Weak convergence of finite measures preserves the integrals of
nonnegative capped Laplace kernels by the bounded-continuous test
characterisation of the weak topology.
-/
theorem solution
    (ν : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hν : Tendsto ν atTop (𝓝 μ)) (s : ℝ) (hs : 0 ≤ s) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(ν n : Measure ℝ))
      atTop
      (𝓝 (∫⁻ x : ℝ,
        ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(μ : Measure ℝ))) := by
  obtain ⟨f, hf⟩ :=
    AvramDividend.Classical.excursion_capped_laplace_bounded_nnreal_test s hs
  have htest :=
    (FiniteMeasure.tendsto_iff_forall_lintegral_tendsto.mp hν) f
  simpa only [← ENNReal.ofReal_coe_nnreal, hf] using htest
