-- Prove2me | solution 1 for BookProof.SqSumFarisLavine.norm_sqSumOp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-02T17:06:39.010468+00:00
-- url     : https://prove2.me/submissions/98b04769-a9c9-48f5-80f6-5524c022e40b

-- Generated from ChapterSqSumFarisLavine.lean — solution of BookProof.SqSumFarisLavine.norm_sqSumOp_le
import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Theorems.Thm_BookProof_SqSumFarisLavine_norm_sqSumPoly_le
import Theorems.Thm_BookProof_SqSumFarisLavine_sqSumOp_pgLp
import Theorems.Thm_BookProof_SqSumFarisLavine_core_eq_pgLp
import Theorems.Thm_BookProof_QgHermiteOscillator_harmCore_pgLp
open BookProof.SqSumFarisLavine




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

variable {D : ℕ} {R : Type*} [Fintype R]

set_option maxHeartbeats 1000000 in
theorem solution {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km B : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (u : polyGaussCore (d := D)) :
    ‖sqSumOp kappa v u‖ ≤ (3 / 2 * km + 8 * B) * ‖harmCore u + (u : L2d D)‖ := by

  obtain ⟨p, hu⟩ := core_eq_pgLp u
  subst hu
  rw [sqSumOp_pgLp, harmCore_pgLp]
  exact norm_sqSumPoly_le hkm hk hB0 hB p
