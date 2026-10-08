-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:06.880889+00:00
-- url     : https://prove2.me/submissions/e597954f-2b5a-446b-b9f9-a1a0778a48b5

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.NSFullData.hasZeroDeficiencyOn_of_total_eigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_total_eigenvectors
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {I : Type*} (e : I → d.D) (lam : I → ℝ)
    (heig : ∀ i, d.hamiltonian (e i) = ((lam i : ℂ)) • e i)
    (htotal : ∀ w : F, (∀ i, (inner ℂ ((e i : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  _root_.BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
      d.D d.hamiltonian e lam heig htotal
