-- Prove2me | solution 1 for BookProof.NsLagrangianDet.one_add_dispGrad
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:21.532227+00:00
-- url     : https://prove2.me/submissions/14262a24-85ae-4b77-beb8-4b4b87d8e64b

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.one_add_dispGrad
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
import Theorems.Thm_BookProof_NsLagrangianDet_phase_zero
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) :
    1 + dispGrad kv y a
      = Matrix.of fun r c => ∑ o : Option (SMode K), ev y (rowCoef kv o r c) * ophase kv a o := by

  ext r c
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Fintype.sum_option]
  simp only [dispGrad, Matrix.of_apply, rowCoef, ophase, owv, phase_zero, mul_one]
  congr 1
  split_ifs <;> simp
