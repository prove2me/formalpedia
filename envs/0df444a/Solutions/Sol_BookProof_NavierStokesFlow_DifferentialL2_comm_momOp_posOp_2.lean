-- Prove2me | solution 2 for BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:54:22.362051+00:00
-- url     : https://prove2.me/submissions/a98692f9-ef39-4b8e-af13-1a5713ced268

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.comm_momOp_posOp
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterMixedLinearEsa
open BookProof.HermiteProductCore

set_option autoImplicit false

open BookProof.NavierStokesFlow.DifferentialL2 MeasureTheory MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato BookProof.FarisLavine BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.LagrangianEsa BookProof.MixedLinearEsa in
theorem e1e53776_polyComm {d : ℕ} (i k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (mulXPoly k p) - mulXPoly k (momPoly i p)
      = C (if i = k then -Complex.I else 0) * p := by
  show C (-Complex.I) * (pderiv i (X k * p) - C (1/2 : ℂ) * (X i * (X k * p)))
      - X k * (C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p))) = _
  rw [Derivation.leibniz, pderiv_X]
  by_cases h : i = k
  · subst h
    simp only [Pi.single_eq_same, if_true, smul_eq_mul]
    ring
  · simp only [Pi.single_apply, Ne.symm h, h, if_false, smul_eq_mul, map_zero]
    ring

set_option maxHeartbeats 1000000 in
open BookProof.NavierStokesFlow.DifferentialL2 MeasureTheory MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato BookProof.FarisLavine BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.LagrangianEsa BookProof.MixedLinearEsa in
theorem solution {d : ℕ} (i k : Fin d) :
    (momOp i).comp (posOp k) - (posOp k).comp (momOp i)
      = (if i = k then -Complex.I else 0) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  have key := e1e53776_polyComm i k ((coreEquiv (d := d)).symm v)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    BookProof.NavierStokesFlow.DifferentialL2.momOp, BookProof.NavierStokesFlow.DifferentialL2.posOp, coreOp, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [← map_sub, key, ← MvPolynomial.smul_eq_C_mul, map_smul, LinearEquiv.apply_symm_apply]
