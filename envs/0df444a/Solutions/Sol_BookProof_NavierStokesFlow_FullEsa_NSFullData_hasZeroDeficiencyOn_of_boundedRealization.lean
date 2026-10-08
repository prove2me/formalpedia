-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:29:59.189308+00:00
-- url     : https://prove2.me/submissions/d1933ce0-20f5-473e-a01c-83a1852530a6

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_boundedRealization
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_hasZeroDeficiencyOn_of_boundedRealization
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in
theorem solution (A : F →L[ℂ] F)
    (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hHA : ∀ x : d.D, (d.hamiltonian x : F) = A (x : F)) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  _root_.BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization
      d.hamiltonian A hsym d.dense hHA
