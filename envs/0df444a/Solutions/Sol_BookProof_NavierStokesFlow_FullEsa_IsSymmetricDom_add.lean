-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:00.255978+00:00
-- url     : https://prove2.me/submissions/d30bb2cb-d20f-4d56-95d6-a16342b675e9

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.IsSymmetricDom.add
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A + B) := by

  intro x y
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_left, inner_add_right, hA x y,
    hB x y]
