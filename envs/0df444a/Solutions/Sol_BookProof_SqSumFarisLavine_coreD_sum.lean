-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.coreD_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T17:54:48.572754+00:00
-- url     : https://prove2.me/submissions/4fc51929-57d8-442c-8f38-76a10f0759c5

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.coreD_sum
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
theorem solution {ι : Type*} (s : Finset ι) (j : Fin D) (f : ι → MvPolynomial (Fin D) ℂ) :
    coreD j (∑ i ∈ s, f i) = ∑ i ∈ s, coreD j (f i) := by

  classical
  induction s using Finset.induction_on with
  | empty => simp [coreD]
  | insert a s ha ih => rw [Finset.sum_insert ha, coreD_add, ih, Finset.sum_insert ha]
