-- Prove2me | solution 1 for BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:42:01.895365+00:00
-- url     : https://prove2.me/submissions/05bf08e3-1035-4972-8da9-06fc2ac9d6ab

-- Generated from ChapterQgOuterFockInteractionFL.lean — solution of BookProof.QgOuterFockInteractionFL.torsionIdx1_ne_torsionIdx2
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Theorems.Thm_BookProof_QuantumGravity3DGauge_idxDE_injective
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFullFL
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterQg3DGaugeEsa
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

noncomputable section

variable (F : QgFamily)

set_option maxHeartbeats 1000000 in
theorem solution {m : Fin 64} (hm : torsionMu m ≠ torsionNu m) :
    torsionIdx1 m ≠ torsionIdx2 m := by

  intro h
  refine hm ?_
  have := idxDE_injective (a₁ := (torsionMu m, torsionNu m, torsionA m))
    (a₂ := (torsionNu m, torsionMu m, torsionA m)) h
  exact congrArg Prod.fst this
