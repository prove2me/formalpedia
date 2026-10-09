-- Prove2me | solution 1 for BookProof.QgOuterFock.sqSumOp_eq_fqOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T23:32:12.060765+00:00
-- url     : https://prove2.me/submissions/1dff90b9-c27c-46f6-9afc-893401bd9c4e

-- Generated from ChapterQgOuterFockEsa.lean — solution of BookProof.QgOuterFock.sqSumOp_eq_fqOp
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Theorems.Thm_BookProof_QgOuterFock_sqSumPoly_eq_fqPoly
open BookProof.QgOuterFock




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.Qg3DGaugeEsa
open BookProof.QgHermiteOscillator
open BookProof.DirectSumEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {R : Type*} [Fintype R] (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    sqSumOp kappa v = fqOp (diagP kappa) (gramQ v) 0 0 0 := by

  rw [sqSumOp, fqOp, sqSumPoly_eq_fqPoly]
