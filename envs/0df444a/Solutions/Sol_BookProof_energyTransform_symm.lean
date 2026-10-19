-- Prove2me | solution 1 for BookProof.energyTransform_symm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:44:34.596629+00:00
-- url     : https://prove2.me/submissions/1b5e195f-c583-4b2f-84f1-876152e5e36a

import Mathlib
import Definitions.Def_ChapterA4
-- Generated from ChapterA4.lean — theorem BookProof.energyTransform_symm
open BookProof



open MeasureTheory




variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

variable (E F : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
theorem solution
    (Θ : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] P)
    (fourierTime : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] (Lp F 2 (volume : Measure E))) :
    (energyTransform E F Θ fourierTime).symm = conjugateₗᵢ Θ fourierTime.symm := by
  ext x
  rfl
