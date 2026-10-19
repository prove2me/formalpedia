-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:39:15.408983+00:00
-- url     : https://prove2.me/submissions/cb3b118c-16a2-4090-8615-5a1ac51c3ada

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.diagUnbounded_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_diagFull_hasZeroDeficiencyOn
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in
theorem solution :
    HasZeroDeficiencyOn diagUnboundedData.D diagUnboundedData.hamiltonian := diagFull_hasZeroDeficiencyOn _ _ _
