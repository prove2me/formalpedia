-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.kin_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T18:40:05.533565+00:00
-- url     : https://prove2.me/submissions/6951d839-000a-4bd3-8c4d-e7618946f6e3

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.kin_mul_comm
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_GaussCoreQuadBounds_coreD_sq_mul
open BookProof.SqSumFarisLavine













open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.FarisLavine
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin D → ℂ) (f p : MvPolynomial (Fin D) ℂ) :
    (∑ j : Fin D, c j • coreD j (coreD j (f * p))) - f * ∑ j : Fin D, c j • coreD j (coreD j p)
      = ∑ j : Fin D, c j • (pderiv j (pderiv j f) * p
          + (2 : ℂ) • (pderiv j f * coreD j p)) := by

  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coreD_sq_mul, mul_smul_comm, ← smul_sub]
  congr 1
  abel
