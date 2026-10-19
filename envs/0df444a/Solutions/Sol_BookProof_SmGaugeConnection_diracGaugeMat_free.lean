-- Prove2me | solution 1 for BookProof.SmGaugeConnection.diracGaugeMat_free
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:23:48.832832+00:00
-- url     : https://prove2.me/submissions/9e7b8f00-9a90-40e3-969e-b1bd5b515d4d

import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmDiracSpinor
-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.diracGaugeMat_free
open BookProof.ChapterCPTHamiltonian
open BookProof.SmDiracSpinor
open BookProof.SmGaugeConnection



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}


theorem solution (k : Fin 3 → ℝ) (m1 m2 g : ℝ)
    (T : Fin d → Matrix (Fin N) (Fin N) ℂ) :
    diracGaugeMat k m1 m2 g T (fun _ _ => (0 : ℝ))
      = diracOneParticle k m1 m2 ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ) := by
  have hc : ∀ j, BookProof.SmGaugeConnection.conn g T (fun _ _ => (0 : ℝ)) j = 0 := by
    intro j; simp [BookProof.SmGaugeConnection.conn]
  unfold BookProof.SmGaugeConnection.diracGaugeMat diracOneParticle diracHamOp
  simp only [hc, add_zero]
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul, Finset.mul_sum, Matrix.one_apply]
  split_ifs <;> simp [Finset.mul_sum, mul_add]
  rw [← Finset.sum_neg_distrib]
  have : ∀ x : Fin 3, -(Complex.I * (Complex.I * ((k x : ℂ) * Kin x i j))) = Kin x i j * (k x : ℂ) := by
    intro x; linear_combination (-((k x : ℂ) * Kin x i j)) * Complex.I_sq
  simp only [this]
  ring

