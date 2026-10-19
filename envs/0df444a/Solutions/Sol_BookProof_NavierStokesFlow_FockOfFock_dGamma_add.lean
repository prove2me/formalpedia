-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.dGamma_add
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:27:16.161219+00:00
-- url     : https://prove2.me/submissions/b127ca62-9d8b-43b2-a03c-f3f265c2c370

import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_add
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]


theorem solution (ω₁ ω₂ : M → ℝ) : dGamma (ω₁ + ω₂) = dGamma ω₁ + dGamma ω₂ := by
  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  show diagCoeff (BookProof.NavierStokesFlow.FockOfFock.confEnergy (ω₁ + ω₂)) _ n
    = diagCoeff (BookProof.NavierStokesFlow.FockOfFock.confEnergy ω₁) _ n
      + diagCoeff (BookProof.NavierStokesFlow.FockOfFock.confEnergy ω₂) _ n
  simp only [diagCoeff, BookProof.NavierStokesFlow.FockOfFock.confEnergy, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  push_cast
  ring

