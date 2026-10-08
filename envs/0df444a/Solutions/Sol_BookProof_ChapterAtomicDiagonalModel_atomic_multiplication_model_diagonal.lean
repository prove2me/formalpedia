-- Prove2me | solution 1 for BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:04:20.825764+00:00
-- url     : https://prove2.me/submissions/7bf01348-d152-4ed9-828b-d7c188b5ee70

-- Generated from ChapterAtomicDiagonalModel.lean — theorem BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal
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
private theorem mult_formula {g : α → ℂ} (hg : MemLp g ⊤ mu) (a : atomSet mu) :
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

theorem solution (hpure : mu (atomSet mu)ᶜ = 0) :
    ∃ B : HilbertBasis (atomSet mu) ℂ (Lp ℂ 2 mu),
      ∀ (g : α → ℂ) (hg : MemLp g ⊤ mu) (a : atomSet mu),
        multOp g hg (B a) = g (a : α) • B a := by
  refine ⟨atomBasis mu hpure, ?_⟩
  have hb : ⇑(atomBasis mu hpure) = atomVec mu :=
    HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  intro g hg a
  rw [hb]
  exact mult_formula mu hg a

#print axioms solution

