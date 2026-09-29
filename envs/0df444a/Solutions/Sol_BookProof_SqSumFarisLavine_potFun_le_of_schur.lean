-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.potFun_le_of_schur
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T19:05:50.307959+00:00
-- url     : https://prove2.me/submissions/30bf2335-906b-4601-87bc-05b0a4e1de9d

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.potFun_le_of_schur
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_schur_bound
import Definitions.Def_ChapterHermiteProductCore
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) :
    potFun v x ≤ (a * b / 2) * ‖x‖ ^ 2 := by

  have hs := schur_bound v ha0 ha hb (fun i => x i)
  rw [← norm_sq_eq_sum x] at hs
  rw [potFun]
  have hlin : ∀ r : R, linFun (v r) x = ∑ i : Fin D, v r i * x i := fun r => rfl
  simp only [hlin]
  linarith
