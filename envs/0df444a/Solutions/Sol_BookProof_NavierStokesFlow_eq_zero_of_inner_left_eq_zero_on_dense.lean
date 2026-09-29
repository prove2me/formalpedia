-- Prove2me | solution 1 for BookProof.NavierStokesFlow.eq_zero_of_inner_left_eq_zero_on_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:04.10566+00:00
-- url     : https://prove2.me/submissions/8643fc21-e505-4845-bf24-8c930044ce2e

-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.eq_zero_of_inner_left_eq_zero_on_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
import Theorems.Thm_BookProof_NavierStokesFlow_eq_zero_of_inner_right_eq_zero_on_dense
open BookProof.NavierStokesFlow









open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (hdense : Dense (D : Set F))
    (w : F) (hw : ∀ v : D, (inner ℂ (v : F) w : ℂ) = 0) : w = 0 :=
  eq_zero_of_inner_right_eq_zero_on_dense hdense w fun v => by
      rw [← inner_conj_symm, hw v, map_zero]
