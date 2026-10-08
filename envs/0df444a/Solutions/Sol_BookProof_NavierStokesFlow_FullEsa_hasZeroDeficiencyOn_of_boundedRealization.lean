-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:56:34.212962+00:00
-- url     : https://prove2.me/submissions/c6860eaf-1835-4f82-a340-879183022caa

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.hasZeroDeficiencyOn_of_boundedRealization
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_hasZeroDeficiencyOn_congr
import Theorems.Thm_BookProof_NavierStokesFlow_hasZeroDeficiencyOn_of_bounded_symmetric
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (H : D →ₗ[ℂ] D)
    (A : F →L[ℂ] F) (hsym : (A : F →ₗ[ℂ] F).IsSymmetric) (hdense : Dense (D : Set F))
    (hHA : ∀ x : D, (H x : F) = A (x : F)) : HasZeroDeficiencyOn D H := by

  have hinv : ∀ v : D, A (v : F) ∈ D := fun v => (hHA v) ▸ (H v).2
  refine hasZeroDeficiencyOn_congr (H₁ := restrictCLM A D hinv) (fun x => (hHA x).symm) ?_
  exact hasZeroDeficiencyOn_of_bounded_symmetric A hsym D hdense hinv
