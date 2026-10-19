-- Prove2me | solution 1 for ContWeatherall.faithful_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:36:24.446564+00:00
-- url     : https://prove2.me/submissions/477a8e04-c35d-405b-b3dc-97bf384a23a9

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff
open ContWeatherall
/-- If some potential exists, `A ↦ dA` is faithful iff `H⁰ = 0`. -/
theorem pl_grad_eq_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (χ₁ χ₂ : E → F) :
    grad χ₁ = grad χ₂ ↔ ∀ x, fderiv ℝ χ₁ x = fderiv ℝ χ₂ x := by
  constructor
  · intro h x
    have hx := congrFun h x
    rw [grad_apply, grad_apply] at hx
    exact (ofSubsingleton ℝ E F (0 : Fin 1)).injective hx
  · intro h
    funext x
    rw [grad_apply, grad_apply, h x]

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) [Nonempty (Pot P)] :
    (fieldStrength P).Faithful ↔ H0Vanishes E F := by
  obtain ⟨A0⟩ := ‹Nonempty (Pot P)›
  constructor
  · intro hf χ hχ hg
    let g : A0 ⟶ A0 := (⟨χ, hχ, by rw [hg, add_zero]⟩ : GaugeHom A0 A0)
    have : g = 𝟙 A0 := (fieldStrength P).map_injective (Subsingleton.elim _ _)
    exact congrArg GaugeHom.chi this
  · intro hH
    refine ⟨fun {A A'} f g _ => GaugeHom.ext ?_⟩
    have hf := f.smooth.differentiable (by simp)
    have hg := g.smooth.differentiable (by simp)
    have hgr : grad f.chi = grad g.chi := by
      have h1 := f.eq
      rw [← g.eq] at h1
      exact (add_left_cancel h1)
    rw [pl_grad_eq_iff] at hgr
    have h0 : grad (f.chi - g.chi) = grad (0 : E → F) := by
      rw [pl_grad_eq_iff]
      intro x
      rw [fderiv_sub (hf x) (hg x), hgr x, sub_self]
      simp
    rw [grad_zero] at h0
    have := hH _ (f.smooth.sub g.smooth) h0
    exact sub_eq_zero.mp this


