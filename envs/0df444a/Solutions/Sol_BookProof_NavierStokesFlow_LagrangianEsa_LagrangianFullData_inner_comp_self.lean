-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:07:09.361471+00:00
-- url     : https://prove2.me/submissions/73ea1552-6c39-496d-99fc-fd95fc00a582

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.inner_comp_self
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (v : D) :
    (inner ℂ (v : F) ((A.comp A) v : F) : ℂ) = ((‖(A v : F)‖ ^ 2 : ℝ) : ℂ) := by

  have h := hA v (A v)
  simp only [LinearMap.comp_apply]
  rw [← h]
  simp
