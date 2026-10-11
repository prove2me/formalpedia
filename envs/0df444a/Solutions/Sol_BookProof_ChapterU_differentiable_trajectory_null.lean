-- Prove2me | solution 1 for BookProof.ChapterU.differentiable_trajectory_null
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:57:08.775544+00:00
-- url     : https://prove2.me/submissions/8dd3cac0-7fac-4273-9e7b-b5ba09332776

-- Generated from ChapterU.lean — solution of BookProof.ChapterU.differentiable_trajectory_null
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
    P {ω | ∃ t, DifferentiableAt ℝ (path ω) t} = 0 := by

  refine MeasureTheory.measure_mono_null (fun ω hω => ?_) hext
  aesop
