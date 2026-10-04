-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T03:24:48.667854+00:00
-- url     : https://prove2.me/submissions/cc24b954-742d-41b0-8619-c2923d5e65e8

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coreEquiv
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_comm_momPoly_mulXPoly
open BookProof.NavierStokesFlow.DifferentialL2




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
-- The core-level commutator unfolds a composite of three linear equivalences, which is
-- elaboration-heavy; the default heartbeat budget is not enough.
theorem solution (i k : Fin d) :
    (momOp i).comp (posOp k) - (posOp k).comp (momOp i)
      = (if i = k then -Complex.I else 0) • LinearMap.id := by

  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := d)).surjective y
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, posOp, momOp, coreOp_coreEquiv,
    LinearMap.smul_apply, LinearMap.id_apply]
  rw [← map_sub, comm_momPoly_mulXPoly, ← MvPolynomial.smul_eq_C_mul, map_smul]
