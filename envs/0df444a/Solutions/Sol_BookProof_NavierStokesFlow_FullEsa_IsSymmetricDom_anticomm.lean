-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:04.587624+00:00
-- url     : https://prove2.me/submissions/8d0ea0f8-d7b8-41bf-a5d1-92d0158a42ba

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.anticomm
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) : IsSymmetricDom (A.comp B + B.comp A) := by

  intro x y
  have h1 : (inner ℂ ((A (B x) : F)) (y : F) : ℂ) = inner ℂ (x : F) ((B (A y) : F)) :=
    (hA _ _).trans (hB _ _)
  have h2 : (inner ℂ ((B (A x) : F)) (y : F) : ℂ) = inner ℂ (x : F) ((A (B y) : F)) :=
    (hB _ _).trans (hA _ _)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_add, inner_add_left,
    inner_add_right, h1, h2]
  ring
