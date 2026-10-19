-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:36:01.817987+00:00
-- url     : https://prove2.me/submissions/9e13250b-dc45-40f7-bc61-f8643c40ab73

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.exists_nsFullData_not_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_jacobiFullData_hamiltonian
import Theorems.Thm_BookProof_NavierStokesFlow_JacobiDeficiency_jacobiOp_not_hasZeroDeficiencyOn
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in

theorem solution :
    ∃ d : NSFullData L2N, ¬ HasZeroDeficiencyOn d.D d.hamiltonian := by
  refine ⟨jacobiFullData, ?_⟩
  rw [jacobiFullData_hamiltonian]
  exact jacobiOp_not_hasZeroDeficiencyOn
