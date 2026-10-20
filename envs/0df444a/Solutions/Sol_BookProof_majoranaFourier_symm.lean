-- Prove2me | solution 1 for BookProof.majoranaFourier_symm
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:10:25.228843+00:00
-- url     : https://prove2.me/submissions/51ff6575-4c10-4b56-a68b-c35fdce26c80

-- Generated from ChapterA4.lean — theorem BookProof.majoranaFourier_symm
import Mathlib
import Definitions.Def_ChapterA4
open BookProof



open MeasureTheory




variable {R E E' : Type*} [Semiring R]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup E'] [Module R E] [Module R E']

variable (E F : Type*) [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
theorem solution
    (Θ : (Lp F 2 (volume : Measure E)) ≃ₗᵢ[ℝ] P) :
    (majoranaFourier E F Θ).symm = conjugateₗᵢ Θ (pauliFourier E F).symm := by 
  ext x
  rfl
