-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_hEx
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:10:41.446153+00:00
-- url     : https://prove2.me/submissions/e01f28d9-156d-4967-a0d2-15fc8fecc936

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_hEx
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution (k : Fin 2) (x : E2) : ‖hEx k x‖ = ‖x k‖ := by
  simp [hEx, norm_smul, EuclideanSpace.norm_single]
#print axioms solution
