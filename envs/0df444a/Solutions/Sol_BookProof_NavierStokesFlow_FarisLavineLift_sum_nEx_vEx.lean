-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.sum_nEx_vEx
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:10:40.036726+00:00
-- url     : https://prove2.me/submissions/206badbd-fff2-49f9-b735-728774252695

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.sum_nEx_vEx
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution : (nEx 0 + nEx 1) vEx = vEx := by
  ext i
  fin_cases i <;> simp [nEx, vEx]
#print axioms solution
