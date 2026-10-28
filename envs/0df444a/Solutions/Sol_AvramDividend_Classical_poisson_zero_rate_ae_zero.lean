-- Prove2me | solution 1 for AvramDividend.Classical.poisson_zero_rate_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:42:41.404689+00:00
-- url     : https://prove2.me/submissions/047a0ce6-2f45-494c-82be-c12b3d1aa0ab

import Mathlib

open ProbabilityTheory MeasureTheory
open scoped ENNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (K : Ω → ℕ)
    (hK : HasLaw K (poissonMeasure 0) P) :
    ∀ᵐ ω ∂P, K ω = 0 := by
  rw [ae_iff]
  rw [hK.measure_eq (p := fun x => ¬ x = 0) (measurableSet_singleton (0 : ℕ)).compl]
  have hc : {x : ℕ | ¬ x = 0} = ({0} : Set ℕ)ᶜ := by ext; simp
  rw [hc, prob_compl_eq_zero_iff (measurableSet_singleton 0), poissonMeasure_singleton]
  simp
