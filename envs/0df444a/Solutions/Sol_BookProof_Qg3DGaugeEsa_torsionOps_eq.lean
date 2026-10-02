-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.torsionOps_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:33:08.780867+00:00
-- url     : https://prove2.me/submissions/94ff268f-3d99-4994-93ed-37c3699dc02d

import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa

noncomputable section

open Finset MvPolynomial BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine BookProof.NavierStokesFlow.DifferentialL2 BookProof.HermiteRelative BookProof.FullQuadratic BookProof.QuantumGravity3DGauge BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent BookProof.Qg3DGaugeEsa in
theorem solution {D : Submodule ℂ (L2d 84)} (Φ : CoreRep 84 D) (m : Fin 64) :
    torsionOps Φ m = Φ.op (mulOp (torsionP m)) := by
  rfl
