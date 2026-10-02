-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.weylProd_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T03:00:03.619276+00:00
-- url     : https://prove2.me/submissions/7ded36b8-4ac9-4c21-9a2e-1f13caf4d84b

import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa

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

open BookProof.YangMillsHermite BookProof.Qg3DGaugeEsa in
theorem solution (S : MvPolynomial (Fin 84) ℂ →ₗ[ℂ] MvPolynomial (Fin 84) ℂ)
    (p : MvPolynomial (Fin 84) ℂ) : weylProd S S p = S (S p) := by
  unfold weylProd
  rw [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, ← two_smul ℂ (S (S p)),
    smul_smul]
  norm_num

end

#print axioms solution
