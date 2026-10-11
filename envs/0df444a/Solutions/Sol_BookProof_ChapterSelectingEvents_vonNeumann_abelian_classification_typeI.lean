-- Prove2me | solution 1 for BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:54.446651+00:00
-- url     : https://prove2.me/submissions/66522100-9984-47bb-99bf-e2ec3ce4e804

-- Generated from ChapterSelectingEvents.lean — solution of BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI
import Mathlib
import Definitions.Def_ChapterSelectingEvents
import Theorems.Thm_BookProof_AbelianDiagonal_vonNeumann_abelian_typeI_case
import Definitions.Def_ChapterAbelianDiagonal
open BookProof.ChapterSelectingEvents



open scoped BigOperators
open MeasureTheory ProbabilityTheory


variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Ω Data : Type*} [MeasurableSpace Ω]

set_option maxHeartbeats 1000000 in
theorem solution
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Function.Injective
        (BookProof.AbelianDiagonal.diagonalStarAlgHom :
          (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ) ∧
      (∀ d e : ι → ℂ,
        Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d) ∧
      (∀ M : Matrix ι ι ℂ,
        (∀ d : ι → ℂ, M * Matrix.diagonal d = Matrix.diagonal d * M) ↔
          ∃ e : ι → ℂ, M = Matrix.diagonal e) := BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case
