-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:16:01.53443+00:00
-- url     : https://prove2.me/submissions/497a2e05-648b-4739-a2d1-de18890694cd

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sum
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_add
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)}
    (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i) := by

  classical
  induction s using Finset.induction with
  | empty => simpa using (IsSymmetricDom.zero (D := D))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hA a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))
