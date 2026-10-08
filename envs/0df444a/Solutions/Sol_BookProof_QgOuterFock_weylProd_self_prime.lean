-- Prove2me | solution 1 for BookProof.QgOuterFock.weylProd_self_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:47:56.071358+00:00
-- url     : https://prove2.me/submissions/d3fe9de4-aca8-44b1-a518-08d37c15d7b9

-- Generated from ChapterQgOuterFockEsa.lean — solution of BookProof.QgOuterFock.weylProd_self'
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

variable {D : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (S : MvPolynomial (Fin D) ℂ →ₗ[ℂ] MvPolynomial (Fin D) ℂ)
    (p : MvPolynomial (Fin D) ℂ) : weylProd S S p = S (S p) := by

  simp only [weylProd, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
  rw [← two_smul ℂ (S (S p)), smul_smul]
  norm_num
