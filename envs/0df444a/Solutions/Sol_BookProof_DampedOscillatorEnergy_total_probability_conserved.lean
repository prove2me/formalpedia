-- Prove2me | solution 1 for BookProof.DampedOscillatorEnergy.total_probability_conserved
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:47:51.165225+00:00
-- url     : https://prove2.me/submissions/23b98399-0d90-43d2-84c9-6b28d2a17d71

-- Generated from ChapterDampedOscillatorEnergy.lean — solution of BookProof.DampedOscillatorEnergy.total_probability_conserved
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
open BookProof.DampedOscillatorEnergy




open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : Measurable T) :
    (μ.map T) Set.univ = 1 := by

  rw [Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ, measure_univ]
