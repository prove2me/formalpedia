-- Prove2me | solution 1 for BookProof.ChapterMeasurementLLN.outcomeIndicator_integral
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:57:48.360792+00:00
-- url     : https://prove2.me/submissions/49a09122-ab1d-4066-9f83-8ac85622a4d4

-- Generated from ChapterMeasurementLLN.lean — solution of BookProof.ChapterMeasurementLLN.outcomeIndicator_integral
import Mathlib
import Definitions.Def_ChapterMeasurementLLN
open BookProof.ChapterMeasurementLLN



open MeasureTheory ProbabilityTheory
open scoped ENNReal


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {k : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M : ℕ → Ω → Fin k) (a : Fin k)
    (hM : Measurable (M 0)) :
    ∫ ω, outcomeIndicator M a 0 ω ∂μ = (μ {ω | M 0 ω = a}).toReal := by

  have hmeas : MeasurableSet (M 0 ⁻¹' {a}) :=
    hM (MeasurableSingletonClass.measurableSet_singleton a)
  have hset : {ω | M 0 ω = a} = M 0 ⁻¹' {a} := rfl
  rw [hset]
  have key : outcomeIndicator M a 0 =
      (M 0 ⁻¹' {a}).indicator 1 := by
    funext ω
    simp [outcomeIndicator, Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
  rw [key, MeasureTheory.integral_indicator_one hmeas]
  rfl
