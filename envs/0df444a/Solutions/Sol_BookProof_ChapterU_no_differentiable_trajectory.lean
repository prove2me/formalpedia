-- Prove2me | solution 1 for BookProof.ChapterU.no_differentiable_trajectory
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:57:07.417304+00:00
-- url     : https://prove2.me/submissions/9d2458d0-51d5-4a49-a2c5-d90e38f8f845

-- Generated from ChapterU.lean — solution of BookProof.ChapterU.no_differentiable_trajectory
import Mathlib
import Definitions.Def_ChapterU
open BookProof.ChapterU



open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]
variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

set_option maxHeartbeats 1000000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (path : Ω → ℝ → ℝ)
    (hext : ∀ᵐ ω ∂P, ∀ t, ¬ DifferentiableAt ℝ (path ω) t) :
    P {ω | ∃ t, DifferentiableAt ℝ (path ω) t}ᶜ = 1 := by

  rw [ MeasureTheory.measure_congr, IsProbabilityMeasure.measure_univ ];
  simp_all [ MeasureTheory.ae_iff ]
