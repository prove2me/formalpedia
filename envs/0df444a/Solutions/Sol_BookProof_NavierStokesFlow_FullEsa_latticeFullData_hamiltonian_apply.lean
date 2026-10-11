-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:46.033988+00:00
-- url     : https://prove2.me/submissions/213ad527-37cf-4e8a-ad89-85044f135bd7

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.latticeFullData_hamiltonian_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_latticeFullData_advection_apply
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.NavierStokesFlow.CanonicalVector

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in

theorem solution (v : Fin 15 → LinfZ) (nu : ℝ)
    (x : (latticeFullData v nu).D) :
    ((latticeFullData v nu).hamiltonian x : L2Z) = latticeFullHamiltonianCLM v nu (x : L2Z) := by
  simp only [NSFullData.hamiltonian, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.comp_apply, Submodule.coe_add, Submodule.coe_sum,
    latticeFullHamiltonianCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hmom : ∀ y : (latticeFullData v nu).D,
      (((latticeFullData v nu).mom i y : (latticeFullData v nu).D) : L2Z) = momentum (y : L2Z) :=
    fun _ => rfl
  rw [hmom, latticeFullData_advection_apply, latticeFullData_advection_apply, hmom]
