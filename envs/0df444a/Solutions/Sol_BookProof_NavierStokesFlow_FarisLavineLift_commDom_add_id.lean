-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.commDom_add_id
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:10:42.191808+00:00
-- url     : https://prove2.me/submissions/e1c7b5d3-6218-48b0-8d75-4a8e9178bf11

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.commDom_add_id
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution (A B : D →ₗ[ℂ] D) :
    commDom A (B + LinearMap.id) = commDom A B := by
  simp [commDom, LinearMap.comp_add, LinearMap.add_comp]
#print axioms solution
