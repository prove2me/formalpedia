-- Prove2me | solution 1 for AvramDividend.Classical.excursion_capped_laplace_tendsto_of_probability_weak
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:17:47.209485+00:00
-- url     : https://prove2.me/submissions/703c35a4-d747-48ef-8ab5-7e11564d7a75

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Theorems.Thm_AvramDividend_Classical_excursion_capped_laplace_bounded_nnreal_test

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology

/-!
Weak convergence of probability measures preserves the integrals
of capped exponential Laplace tests. Their bounded-continuous
NNReal lift is supplied by the preceding excursion helper.
-/
theorem solution
    (P : ℕ → ProbabilityMeasure ℝ) (Q : ProbabilityMeasure ℝ)
    (hP : Tendsto P atTop (𝓝 Q)) (s : ℝ) (hs : 0 ≤ s) :
    Tendsto
      (fun n : ℕ =>
        ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(P n : Measure ℝ))
      atTop
      (𝓝 (∫⁻ x : ℝ,
        ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂(Q : Measure ℝ))) := by
  obtain ⟨f, hf⟩ :=
    AvramDividend.Classical.excursion_capped_laplace_bounded_nnreal_test s hs
  have htest :=
    (ProbabilityMeasure.tendsto_iff_forall_lintegral_tendsto.mp hP) f
  simpa only [← ENNReal.ofReal_coe_nnreal, hf] using htest
