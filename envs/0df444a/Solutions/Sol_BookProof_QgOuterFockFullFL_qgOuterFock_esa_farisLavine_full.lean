-- Prove2me | solution 1 for BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T20:32:49.972507+00:00
-- url     : https://prove2.me/submissions/7b287bde-0280-4c0b-8c39-473a78b576b6

-- Generated from ChapterQgOuterFockFullFL.lean — solution of BookProof.QgOuterFockFullFL.qgOuterFock_esa_farisLavine_full
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Theorems.Thm_BookProof_QgOuterFockFullFL_qgFLc_nonneg
import Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_symmetricOn
import Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_core
import Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_rel
import Theorems.Thm_BookProof_QgOuterFockFullFL_qgSectorExt_commForm_le
import Theorems.Thm_BookProof_QgOuterFockFL_qgOuterFock_esa_farisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.QgOuterFockFullFL




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open Filter Topology
open BookProof.HermiteProductCore
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution :
    EssentiallySelfAdjointOn qgOuterFriedDom
        (dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel) ∧
      ∀ x : qgOuterCore, ∃ h : (x : BookProof.QgOuterFockFL.qgOuterFock) ∈ qgOuterFriedDom,
        dsFibOp (fun n : ℕ => harmFried (n * 84)) qgSectorExt qgFLK qgSectorExt_rel
            ⟨(x : BookProof.QgOuterFockFL.qgOuterFock), h⟩ = qgOuterHam x :=
  qgOuterFock_esa_farisLavine qgSectorExt qgSectorExt_symmetricOn qgSectorExt_core
      qgFLK qgFLc qgFLc_nonneg qgSectorExt_rel qgSectorExt_commForm_le
