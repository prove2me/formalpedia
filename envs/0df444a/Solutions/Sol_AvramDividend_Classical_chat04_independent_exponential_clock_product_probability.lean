-- Prove2me | solution 1 for AvramDividend.Classical.chat04_independent_exponential_clock_product_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:26:03.873918+00:00
-- url     : https://prove2.me/submissions/aae5fd63-4c4c-43af-a019-04d4ef17eb32

import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p) :
    ∃ R : Measure (Ω × ℝ),
      IsProbabilityMeasure R ∧
      R.fst = P ∧
      R.snd = ProbabilityTheory.expMeasure p := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  refine ⟨P.prod (ProbabilityTheory.expMeasure p), inferInstance, ?_, ?_⟩
  · exact Measure.fst_prod
  · exact Measure.snd_prod
