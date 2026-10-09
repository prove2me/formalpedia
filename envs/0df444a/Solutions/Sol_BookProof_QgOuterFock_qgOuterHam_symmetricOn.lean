-- Prove2me | solution 1 for BookProof.QgOuterFock.qgOuterHam_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T22:52:20.844144+00:00
-- url     : https://prove2.me/submissions/f236ec31-0ba7-4b33-b248-25bc0686c049

-- Generated from ChapterQgOuterFockEsa.lean — solution of BookProof.QgOuterFock.qgOuterHam_symmetricOn
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
import Theorems.Thm_BookProof_QgOuterFock_qgSectorHam_symmetricOn
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
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
theorem solution : SymmetricOn qgOuterCore qgOuterHam := dsOp_symmetricOn _ fun n => qgSectorHam_symmetricOn n
