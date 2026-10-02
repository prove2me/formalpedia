-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.qgSignedPoly_apply
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:51:02.022297+00:00
-- url     : https://prove2.me/submissions/71014faa-93b4-49db-989c-2848d306d2a7

import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.Qg3DGaugeEsa in
theorem solution (kappa : Fin 84 → ℝ) (p : MvPolynomial (Fin 84) ℂ) :
    qgSignedPoly kappa p
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ j : Fin 84, ((kappa j : ℝ) : ℂ) • pmom j (pmom j p))
            + ∑ m : Fin 64, torsionP m * (torsionP m * p)) := by
  simp only [qgSignedPoly, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, mulOp, LinearMap.mulLeft_apply]
