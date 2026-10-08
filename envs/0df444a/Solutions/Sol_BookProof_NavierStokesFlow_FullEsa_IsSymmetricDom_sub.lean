-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:01.548607+00:00
-- url     : https://prove2.me/submissions/edc3dc60-5c3f-4d4f-a452-7354bbb2ac83

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.sub
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A - B) := by

  intro x y
  simp only [LinearMap.sub_apply, Submodule.coe_sub, inner_sub_left, inner_sub_right, hA x y,
    hB x y]
