-- Prove2me | solution 1 for BookProof.QgOuterFockFullFL.qgSectorExt_rel
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T20:11:50.074719+00:00
-- url     : https://prove2.me/submissions/6ac8578b-484c-4e47-9903-866a2c389706

-- Generated from ChapterQgOuterFockFullFL.lean — solution of BookProof.QgOuterFockFullFL.qgSectorExt_rel
import Mathlib
import Definitions.Def_ChapterQgOuterFockFullFL
import Theorems.Thm_BookProof_QgOuterFockCoreFL_CoreData_ext_norm_le
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterHermiteProductCore
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
open BookProof.QgOuterFockFL

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (n : ℕ) (u : (harmFried (n * 84)).dom),
    ‖qgSectorExt n u‖ ≤ qgFLK * ‖(harmFried (n * 84)).op u + (u : L2d (n * 84))‖ := fun n u => (qgSectorData n).ext_norm_le u
