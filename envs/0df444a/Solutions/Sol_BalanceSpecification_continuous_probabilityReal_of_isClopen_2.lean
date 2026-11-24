-- Prove2me | solution 2 for BalanceSpecification.continuous_probabilityReal_of_isClopen
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:13:55.385198+00:00
-- url     : https://prove2.me/submissions/b963f7c7-45f6-458d-a32d-1b1b91d0684a

import Mathlib
open MeasureTheory Filter Set Topology


theorem solution {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω] {E : Set Ω} (hE : IsClopen E) :
    Continuous (fun μ : ProbabilityMeasure Ω => (μ : Measure Ω).real E) := by
  apply continuous_iff_continuousAt.mpr; intro μ
  have h := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto (μ := μ) (μs := id) tendsto_id hE
  simpa [ContinuousAt, Function.comp_def] using (NNReal.continuous_coe.tendsto _).comp h
