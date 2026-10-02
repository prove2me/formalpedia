-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.coreRepPoly_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T02:08:56.534593+00:00
-- url     : https://prove2.me/submissions/9dbd80ca-e6fb-475a-8c05-8598dca66ba9

import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa

noncomputable section

open BookProof.Qg3DGaugeEsa Finset MvPolynomial BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine BookProof.NavierStokesFlow.DifferentialL2 BookProof.HermiteRelative BookProof.FullQuadratic BookProof.QuantumGravity3DGauge BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent in
theorem solution (p : MvPolynomial (Fin 84) ℂ) :
    (coreRepPoly 84).equiv p = coreEquiv p := by
  apply Subtype.ext
  rfl

end

#print axioms solution
