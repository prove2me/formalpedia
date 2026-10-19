-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:23:09.416032+00:00
-- url     : https://prove2.me/submissions/ed52b211-c591-49a8-a327-4ba968201e3e

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.linearFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_halfLineFull_hasZeroDeficiencyOn
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_linearFullData_symbol
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_not_summable_nsCoupling_linear
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution :
    HasZeroDeficiencyOn linearFullData.D linearFullData.hamiltonian := by

  refine halfLineFull_hasZeroDeficiencyOn linearMode 1 ?_
  rw [linearFullData_symbol]
  exact not_summable_nsCoupling_linear
