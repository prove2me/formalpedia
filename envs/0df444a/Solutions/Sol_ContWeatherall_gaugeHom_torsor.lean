-- Prove2me | solution 1 for ContWeatherall.gaugeHom_torsor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:34:30.0761+00:00
-- url     : https://prove2.me/submissions/97971667-9e62-4c49-9132-ff31c540b582

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff
open ContWeatherall
/-- `Hom(A, A')` is an `F`-torsor: shifting a gauge arrow by a constant gives a gauge arrow, and
any two parallel gauge arrows differ by a unique constant. -/
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

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop} {A A' : Pot P} (f : A ⟶ A') :
    (∀ c : F, ∃ g : A ⟶ A', g.chi = f.chi + fun _ => c) ∧
      ∀ g : A ⟶ A', ∃! c : F, g.chi = f.chi + fun _ => c := by
  have hf := f.smooth.differentiable (by simp)
  constructor
  · intro c
    refine ⟨(⟨f.chi + fun _ => c, f.smooth.add contDiff_const, ?_⟩ : GaugeHom A A'), rfl⟩
    have : grad (f.chi + fun _ => c) = grad f.chi := by
      rw [pl_grad_eq_iff]
      intro x
      exact fderiv_add_const (f := f.chi) c
    rw [this]
    exact f.eq
  · intro g
    have hg := g.smooth.differentiable (by simp)
    have hgr : grad g.chi = grad f.chi := by
      have h1 := g.eq
      rw [← f.eq] at h1
      exact (add_left_cancel h1)
    rw [pl_grad_eq_iff] at hgr
    have hd : ∀ x, fderiv ℝ (g.chi - f.chi) x = 0 := by
      intro x
      rw [fderiv_sub (hg x) (hf x), hgr x, sub_self]
    have hc := is_const_of_fderiv_eq_zero (hg.sub hf) hd
    refine ⟨g.chi 0 - f.chi 0, ?_, ?_⟩
    · funext x
      have := hc x 0
      simp only [Pi.sub_apply] at this
      simp only [Pi.add_apply]
      rw [← this]
      abel
    · intro c hc'
      have := congrFun hc' 0
      simp only [Pi.add_apply] at this
      rw [this]
      abel


