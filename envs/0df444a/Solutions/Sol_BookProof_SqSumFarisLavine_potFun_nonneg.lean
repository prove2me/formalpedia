-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.potFun_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T17:54:52.318124+00:00
-- url     : https://prove2.me/submissions/c80f34da-166b-4c31-b6c9-b16eb2ce27e0

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.potFun_nonneg
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (v : R → Fin D → ℝ) (x : Vd D) : 0 ≤ potFun v x := by

  rw [potFun]
  have : (0 : ℝ) ≤ ∑ r : R, (linFun (v r) x) ^ 2 :=
    Finset.sum_nonneg fun r _ => sq_nonneg _
  linarith
