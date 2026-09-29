-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.sum_hEx_vEx
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:10:39.315663+00:00
-- url     : https://prove2.me/submissions/7ca38dca-d369-41e4-aa0d-c501496a5e5c

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.sum_hEx_vEx
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}
set_option autoImplicit false

theorem solution :
    (hEx 0 + hEx 1) vEx = (2 : ℂ) • EuclideanSpace.single (0 : Fin 2) (1 : ℂ) := by
  ext i
  fin_cases i <;> norm_num [hEx, vEx]
#print axioms solution
