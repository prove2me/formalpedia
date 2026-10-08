-- Prove2me | solution 1 for BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:19.012543+00:00
-- url     : https://prove2.me/submissions/56bf3f5e-3461-4d4b-8c5e-e4f99710cc41

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.atomVec_coeFn
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


theorem solution (a : atomSet mu) :
    (atomVec mu a : α → ℂ) =ᵐ[mu] fun x =>
      (((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ) : ℂ) *
        Set.indicator {(a : α)} (fun _ => (1 : ℂ)) x := by
  filter_upwards [Lp.coeFn_smul
    ((((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ)) : ℂ)
    (atomIndicator mu (a : α)), atomIndicator_coeFn mu (a : α)] with x hs hi
  simpa [atomVec, hi, smul_eq_mul] using hs

#print axioms solution

