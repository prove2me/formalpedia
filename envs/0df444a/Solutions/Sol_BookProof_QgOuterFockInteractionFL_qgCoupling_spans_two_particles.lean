-- Prove2me | solution 1 for BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:43:00.684071+00:00
-- url     : https://prove2.me/submissions/d0521d62-2db0-4f45-b010-150e11a0be27

-- Generated from ChapterQgOuterFockInteractionFL.lean — solution of BookProof.QgOuterFockInteractionFL.qgCoupling_spans_two_particles
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Theorems.Thm_BookProof_QgOuterFockInteractionFL_torsionVec_self
import Theorems.Thm_BookProof_QgOuterFock_modeOf_pcoord
import Theorems.Thm_BookProof_QgOuterFock_partOf_pcoord
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.QgOuterFockInteractionFL




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine
open BookProof.Qg3DGaugeEsa
open BookProof.QgOuterFock

noncomputable section

variable (F : QgFamily)

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) {n : ℕ} (p : Fin n)
    (hp : nextPart p ≠ p) {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) :
    qgIntVec lam n (Sum.inr (p, m)) (pcoord p (torsionIdx1 m)) = lam ∧
      qgIntVec lam n (Sum.inr (p, m)) (pcoord (nextPart p) (torsionIdx1 m)) = -lam := by

  have hone := torsionVec_self hm
  constructor
  · change lam * (qgTorsionVecN n (p, m) (pcoord p (torsionIdx1 m))
        - qgTorsionVecN n (nextPart p, m) (pcoord p (torsionIdx1 m))) = lam
    rw [qgTorsionVecN, qgTorsionVecN, partOf_pcoord, modeOf_pcoord, if_pos rfl,
      if_neg (fun h => hp h.symm), hone]
    ring
  · change lam * (qgTorsionVecN n (p, m) (pcoord (nextPart p) (torsionIdx1 m))
        - qgTorsionVecN n (nextPart p, m) (pcoord (nextPart p) (torsionIdx1 m))) = -lam
    rw [qgTorsionVecN, qgTorsionVecN, partOf_pcoord, modeOf_pcoord, if_pos rfl, if_neg hp,
      hone]
    ring
