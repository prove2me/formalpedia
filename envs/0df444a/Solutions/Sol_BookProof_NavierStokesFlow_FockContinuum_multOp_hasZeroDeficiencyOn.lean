-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockContinuum.multOp_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:16:26.287637+00:00
-- url     : https://prove2.me/submissions/ede22f3f-6c1f-4eff-88b7-9fb720cbf653

import Mathlib
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
-- Generated from ChapterNavierStokesFockContinuum.lean — theorem BookProof.NavierStokesFlow.FockContinuum.multOp_hasZeroDeficiencyOn
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockContinuum


open MeasureTheory



open FullEsa

variable {X : Type*} [MeasurableSpace X]


theorem solution (μ : Measure X) {g : X → ℝ} (hg : Measurable g) :
    HasZeroDeficiencyOn (boundedEnergyCore μ g) (multOp μ hg) := by
  exact BookProof.NavierStokesFlow.FockLagrangian.mulD_hasZeroDeficiencyOn μ hg hg
    (BookProof.NavierStokesFlow.FockLagrangian.DominatedOn.rfl' μ g)

