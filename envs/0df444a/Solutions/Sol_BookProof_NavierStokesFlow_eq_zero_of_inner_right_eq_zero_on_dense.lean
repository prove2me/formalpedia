-- Prove2me | solution 1 for BookProof.NavierStokesFlow.eq_zero_of_inner_right_eq_zero_on_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T00:25:11.914286+00:00
-- url     : https://prove2.me/submissions/e1cf0240-7628-4e48-88e9-cb72c3afcdd7

-- Generated from ChapterNavierStokesEsa.lean — solution of BookProof.NavierStokesFlow.eq_zero_of_inner_right_eq_zero_on_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow









open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

set_option maxHeartbeats 1000000 in
theorem solution {D : Submodule ℂ F} (hdense : Dense (D : Set F))
    (w : F) (hw : ∀ v : D, (inner ℂ w (v : F) : ℂ) = 0) : w = 0 := by

  have hcont : Continuous fun y : F => (inner ℂ w y : ℂ) := (innerSL ℂ w).continuous
  have hall : (fun y : F => (inner ℂ w y : ℂ)) = fun _ => 0 :=
    Continuous.ext_on hdense hcont continuous_const fun x hx => hw ⟨x, hx⟩
  exact inner_self_eq_zero.mp (congrFun hall w)
