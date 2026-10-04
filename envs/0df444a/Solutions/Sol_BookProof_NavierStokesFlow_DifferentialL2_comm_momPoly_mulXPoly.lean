-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.comm_momPoly_mulXPoly
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:35:19.73926+00:00
-- url     : https://prove2.me/submissions/0586015e-f43e-4191-a3f4-fd27188e1d35

import Definitions.Def_ChapterHermiteProductCore
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

set_option autoImplicit false

open BookProof.NavierStokesFlow.DifferentialL2 MeasureTheory MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato BookProof.FarisLavine BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.LagrangianEsa in
theorem solution {d : ℕ} (i k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (mulXPoly k p) - mulXPoly k (momPoly i p)
      = C (if i = k then -Complex.I else 0) * p := by
  show C (-Complex.I) * (pderiv i (X k * p) - C (1/2 : ℂ) * (X i * (X k * p)))
      - X k * (C (-Complex.I) * (pderiv i p - C (1/2 : ℂ) * (X i * p))) = _
  rw [Derivation.leibniz, pderiv_X]
  by_cases h : i = k
  · subst h
    simp only [Pi.single_eq_same, if_true, smul_eq_mul, map_one]
    ring
  · simp only [Pi.single_apply, Ne.symm h, h, if_false, smul_zero, smul_eq_mul, map_zero]
    ring
