-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_nEx
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:10:40.756646+00:00
-- url     : https://prove2.me/submissions/ca0ef24d-e9b6-4fa5-b119-911ac468f3a4

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_nEx
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution (k : Fin 2) (x : E2) : ‖nEx k x‖ = ‖x k‖ := by
  simp [nEx, norm_smul, EuclideanSpace.norm_single]
#print axioms solution
