-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:47.130481+00:00
-- url     : https://prove2.me/submissions/487bbad4-4739-419b-b79d-7043e9d8089f

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.latticeFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_hasZeroDeficiencyOn_of_boundedRealization
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_NSFullData_hasZeroDeficiencyOn_of_boundedRealization
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullHamiltonianCLM_isSymmetric
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullData_hamiltonian_apply
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.ChapterContinuityUnitaryInfinite

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ) :
    HasZeroDeficiencyOn (latticeFullData v nu).D (latticeFullData v nu).hamiltonian :=
  (latticeFullData v nu).hasZeroDeficiencyOn_of_boundedRealization
    (latticeFullHamiltonianCLM v nu) (latticeFullHamiltonianCLM_isSymmetric v nu)
    (latticeFullData_hamiltonian_apply v nu)
