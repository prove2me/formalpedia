-- Prove2me | solution 1 for BookProof.ChapterAtomicDiagonalModel.multOp_atomVec
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:16.306956+00:00
-- url     : https://prove2.me/submissions/3cc462fb-15fd-4587-9b55-a7223c114550

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.multOp_atomVec
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Mathlib
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterAtomicDiagonalModel


noncomputable section

open MeasureTheory


open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (mu : Measure α) [IsFiniteMeasure mu]

private theorem vec_formula (a : atomSet mu) :
    (atomVec mu a : α → ℂ) =ᵐ[mu] fun x =>
      (((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ) : ℂ) *
        Set.indicator {(a : α)} (fun _ => (1 : ℂ)) x := by
  filter_upwards [Lp.coeFn_smul
    ((((Real.sqrt (mu.real {(a : α)}))⁻¹ : ℝ)) : ℂ)
    (atomIndicator mu (a : α)), atomIndicator_coeFn mu (a : α)] with x hs hi
  simpa [atomVec, hi, smul_eq_mul] using hs

theorem solution {g : α → ℂ} (hg : MemLp g ⊤ mu) (a : atomSet mu) :
    multOp g hg (atomVec mu a) = g (a : α) • atomVec mu a := by
  refine Lp.ext ?_
  have hm : (multOp g hg (atomVec mu a) : α → ℂ) =ᵐ[mu]
      fun x => g x * (atomVec mu a : α → ℂ) x :=
    MemLp.coeFn_toLp (mul_memLp_two hg (atomVec mu a))
  filter_upwards [hm, vec_formula mu a, Lp.coeFn_smul (g (a : α)) (atomVec mu a)]
    with x hm hx hs
  rw [hm, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hx]
  by_cases h : x = (a : α)
  · subst x
    rfl
  · simp [Set.indicator_of_notMem, h]

#print axioms solution

