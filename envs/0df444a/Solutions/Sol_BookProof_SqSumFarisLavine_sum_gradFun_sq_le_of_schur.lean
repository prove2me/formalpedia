-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:23.153605+00:00
-- url     : https://prove2.me/submissions/1757d738-7f01-4734-93c1-9a1af8ed0040

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.sum_gradFun_sq_le_of_schur
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_schur_bound
import Theorems.Thm_BookProof_SqSumFarisLavine_potFun_le_of_schur
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) :
    ∑ k : Fin D, (gradFun v k x) ^ 2 ≤ (a * b) ^ 2 * ‖x‖ ^ 2 := by

  have hs := schur_bound (fun (k : Fin D) (r : R) => v r k) hb0
    (fun k => hb k) (fun r => ha r) (fun r => linFun (v r) x)
  have hgrad : ∀ k : Fin D, gradFun v k x = ∑ r : R, v r k * linFun (v r) x := fun k => rfl
  simp only [hgrad]
  have hpot := potFun_le_of_schur ha0 ha hb x
  have hsum : ∑ r : R, (linFun (v r) x) ^ 2 = 2 * potFun v x := by
    rw [potFun]; ring
  rw [hsum] at hs
  have hab : 0 ≤ b * a := mul_nonneg hb0 ha0
  nlinarith [hs, hpot, norm_nonneg x, sq_nonneg ‖x‖]
