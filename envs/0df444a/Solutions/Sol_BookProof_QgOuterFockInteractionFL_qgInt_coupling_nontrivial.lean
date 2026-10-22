-- Prove2me | solution 1 for BookProof.QgOuterFockInteractionFL.qgInt_coupling_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T04:46:43.8016+00:00
-- url     : https://prove2.me/submissions/fc493da4-4c8e-4ad8-90e8-5e07964a0f09

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
import Mathlib
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.Qg3DGaugeEsa
open BookProof.QgOuterFock
open BookProof.QgOuterFockInteractionFL



open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.QgOuterFockFL BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockFullFL
open BookProof.Qg3DGaugeEsa BookProof.QuantumGravity3DGauge
open BookProof.GaussCoreQuadBounds BookProof.SqSumFarisLavine

noncomputable section

variable (F : QgFamily)

theorem solution {lam : ℝ} (hlam : lam ≠ 0) {n : ℕ} (hn : 2 ≤ n) :
    ∃ (r : (Fin n × Fin 64) ⊕ (Fin n × Fin 64)) (I J : Fin (n * 84)),
      partOf I ≠ partOf J ∧ qgIntVec lam n r I ≠ 0 ∧ qgIntVec lam n r J ≠ 0 := by
  set p0 : Fin n := ⟨0, by omega⟩ with hp0
  have hp1 : nextPart p0 ≠ p0 := by
    intro h
    have := congrArg Fin.val h
    rw [nextPart_val] at this
    simp [hp0] at this
    omega
  have hne : torsionIdx1 4 ≠ torsionIdx2 4 := by decide
  have tv1 : torsionVec 4 (torsionIdx1 4) = 1 := by simp [torsionVec, hne]
  refine ⟨Sum.inr (p0, 4), finProdFinEquiv (p0, torsionIdx1 4),
    finProdFinEquiv (nextPart p0, torsionIdx1 4), ?_, ?_, ?_⟩
  · simpa [partOf] using hp1.symm
  · simp [qgIntVec, qgCouplingVec, qgTorsionVecN, partOf, modeOf, hp1.symm, tv1, hlam]
  · simp [qgIntVec, qgCouplingVec, qgTorsionVecN, partOf, modeOf, hp1, tv1, hlam]
