-- Prove2me | solution 1 for BookProof.QgOuterFock.dsOp_quadForm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-01T14:54:59.70099+00:00
-- url     : https://prove2.me/submissions/4b929d25-448d-415f-be24-1f5483d70fd4

-- Generated from ChapterQgOuterFockEsa.lean — solution of BookProof.QgOuterFock.dsOp_quadForm_nonneg
import Mathlib
import Definitions.Def_ChapterQgOuterFockEsa
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

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)} (H : ∀ i, D i →ₗ[ℂ] G i)
    (hpos : ∀ (i : ι) (u : D i), 0 ≤ quadForm (H i) u) (x : dsCore D) :
    0 ≤ quadForm (dsOp H) x := by

  have hsum : HasSum (fun i => (inner ℂ ((x : lp G 2) i) ((dsOp H x : lp G 2) i) : ℂ))
      (inner ℂ (x : lp G 2) (dsOp H x : lp G 2)) := lp.hasSum_inner _ _
  have hre := Complex.reCLM.hasSum hsum
  refine hasSum_le (fun i => ?_) hasSum_zero hre
  exact hpos i ⟨(x : lp G 2) i, x.2.2 i⟩
