-- Prove2me | solution 1 for FamousTheorems.portmanteau_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:44:18.60459+00:00
-- url     : https://prove2.me/submissions/3cf140c8-bad7-4070-b394-26e07b5bd9b6

import Mathlib

theorem solution {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]
    {L : Filter ι} [L.IsCountablyGenerated] (μ : MeasureTheory.ProbabilityMeasure Ω)
    (μs : ι → MeasureTheory.ProbabilityMeasure Ω) :
    (Filter.Tendsto μs L (nhds μ) ↔ ∀ F : Set Ω, IsClosed F →
        Filter.limsup (fun i => (μs i : MeasureTheory.Measure Ω) F) L ≤ (μ : MeasureTheory.Measure Ω) F) ∧
      (Filter.Tendsto μs L (nhds μ) ↔ ∀ G : Set Ω, IsOpen G →
        (μ : MeasureTheory.Measure Ω) G ≤ Filter.liminf (fun i => (μs i : MeasureTheory.Measure Ω) G) L) :=
  ⟨⟨fun h _ hF => MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h hF,
    MeasureTheory.tendsto_of_forall_isClosed_limsup_le'⟩,
   ⟨fun h _ hG => MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hG,
    MeasureTheory.tendsto_of_forall_isOpen_le_liminf'⟩⟩
