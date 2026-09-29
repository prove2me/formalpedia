-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.lagT_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T09:56:37.758709+00:00
-- url     : https://prove2.me/submissions/934bbab3-9dc4-4f8f-8238-7cd1776ada2e

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — solution of BookProof.NavierStokesFlow.LagrangianCanonical.lagT_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_lagT_coreState
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianCanonical_coreState_total
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_total_eigenvectors
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical

















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution : HasZeroDeficiencyOn (lpFiniteModes Vel) (lagT nu) :=
  hasZeroDeficiencyOn_of_total_eigenvectors _ _ coreState (lagLam nu)
      (lagT_coreState nu) coreState_total
