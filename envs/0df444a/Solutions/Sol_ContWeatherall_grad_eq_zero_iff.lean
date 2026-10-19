-- Prove2me | solution 1 for ContWeatherall.grad_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:33:03.433551+00:00
-- url     : https://prove2.me/submissions/dc37039f-b577-40c5-b86c-383308ee0d14

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff
open ContWeatherall
/-- Degree 0: a differentiable function has `dχ = 0` iff it is constant. -/
theorem pl_grad_eq_zero_iff_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (χ : E → F) :
    grad χ = 0 ↔ ∀ x, fderiv ℝ χ x = 0 := by
  constructor
  · intro h x
    have hx := congrFun h x
    rw [grad_apply] at hx
    apply (ofSubsingleton ℝ E F (0 : Fin 1)).injective
    rw [hx]
    ext v
    simp
  · intro h
    funext x
    rw [grad_apply, h x]
    ext v
    simp

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {χ : E → F} (hχ : Differentiable ℝ χ) :
    grad χ = 0 ↔ ∃ c : F, χ = fun _ => c := by
  rw [pl_grad_eq_zero_iff_fderiv]
  constructor
  · intro h
    refine ⟨χ 0, ?_⟩
    funext x
    exact is_const_of_fderiv_eq_zero hχ h x 0
  · rintro ⟨c, rfl⟩ x
    exact fderiv_const_apply c


