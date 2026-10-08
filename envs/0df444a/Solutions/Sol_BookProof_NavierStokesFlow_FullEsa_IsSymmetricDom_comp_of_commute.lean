-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:03.006053+00:00
-- url     : https://prove2.me/submissions/647dd87c-1a8b-4625-bfa2-15825d9fb624

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.comp_of_commute
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom (A.comp B) := by

  intro x y
  have h1 : (inner ℂ ((A (B x) : F)) (y : F) : ℂ) = inner ℂ ((B x : F)) ((A y : F)) := hA _ _
  have h2 : (inner ℂ ((B x : F)) ((A y : F)) : ℂ) = inner ℂ (x : F) ((B (A y) : F)) := hB _ _
  have h3 : B (A y) = A (B y) := by
    have := congrArg (fun T : D →ₗ[ℂ] D => T y) hcomm
    simpa using this.symm
  simpa [h3] using h1.trans h2
