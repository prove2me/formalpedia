-- Prove2me | solution 1 for BookProof.ChapterAtomicDiagonalModel.coe_atomBasis
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:14.333411+00:00
-- url     : https://prove2.me/submissions/a076c07a-84c0-4324-b61f-516d3357d2b6

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.coe_atomBasis
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterAtomicDiagonalModel
open BookProof.ChapterAtomicDiagonalModel


noncomputable section

open MeasureTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (mu : Measure α) [IsFiniteMeasure mu]


theorem solution (hpure : mu (atomSet mu)ᶜ = 0) :
    ⇑(atomBasis mu hpure) = atomVec mu := by
  exact HilbertBasis.coe_mkOfOrthogonalEqBot _ _

#print axioms solution

