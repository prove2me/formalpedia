-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.pgLp_qgSignedPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:50:36.097986+00:00
-- url     : https://prove2.me/submissions/6dc7012e-5960-473e-87e2-6faa3e055daa

-- Generated from ChapterQg3DGaugeEsa.lean — solution of BookProof.Qg3DGaugeEsa.pgLp_qgSignedPoly
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSignedPoly_apply
import Theorems.Thm_BookProof_Qg3DGaugeEsa_pgLp_eq_pgMap
open BookProof.Qg3DGaugeEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (kappa : Fin 84 → ℝ) (p : MvPolynomial (Fin 84) ℂ) :
    pgLp (qgSignedPoly kappa p)
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ j : Fin 84, ((kappa j : ℝ) : ℂ) • pgLp (pmom j (pmom j p)))
            + ∑ m : Fin 64, pgLp (torsionP m * (torsionP m * p))) := by

  rw [qgSignedPoly_apply]
  simp only [pgLp_eq_pgMap, map_smul, map_add, map_sum]
