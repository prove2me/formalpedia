-- Prove2me | solution 1 for AvramDividend.Classical.chat04_independent_exponential_clock_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:31:37.845068+00:00
-- url     : https://prove2.me/submissions/18258223-7d1a-4dfd-8604-9268b70012c7

import Mathlib
open MeasureTheory ProbabilityTheory
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p) :
    IndepFun
      (fun z : Ω × ℝ => z.1)
      (fun z : Ω × ℝ => z.2)
      (P.prod (ProbabilityTheory.expMeasure p)) := by
  have : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
