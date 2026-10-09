-- Prove2me | solution 1 for BookProof.QgOuterFock.qgSectorHam_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:18.859673+00:00
-- url     : https://prove2.me/submissions/9646873c-b260-4ffb-8e78-9ba0e89661d7

-- Generated from ChapterQgOuterFockEsa.lean — solution of BookProof.QgOuterFock.qgSectorHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Theorems.Thm_BookProof_QgOuterFock_sqSumOp_symmetricOn
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
theorem solution (n : ℕ) :
    SymmetricOn (polyGaussCore (d := n * 84)) (qgSectorHam n) := sqSumOp_symmetricOn _ _
