-- Prove2me | solution 1 for ContinuityEqWiki.div_velocity_eq_zero_of_incompressible
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:14:45.733311+00:00
-- url     : https://prove2.me/submissions/1c6b9166-3667-425d-9f96-aa9434adf932

import Mathlib
import Definitions.Def_ContinuityEqWiki_Defs

open ContinuityEqWiki

theorem solution (ρ : ℝ → Space → ℝ) (u : ℝ → Space → Space)
    (hρ : ContDiff ℝ 1 (Function.uncurry ρ)) (hu : ∀ t, ContDiff ℝ 1 (u t))
    (hpos : ∀ t x, 0 < ρ t x)
    (mass : ∀ t x, timeDeriv ρ t x + div (fun y => ρ t y • u t y) x = 0)
    (incompressible : ∀ t x, timeDeriv ρ t x + ∑ i, u t x i * partialDeriv i (ρ t) x = 0) :
    ∀ t x, div (u t) x = 0 := by
  intro t x
  have hρt : DifferentiableAt ℝ (ρ t) x := by
    have h1 : DifferentiableAt ℝ (fun y : Space => ((t, y) : ℝ × Space)) x :=
      (differentiableAt_const t).prodMk differentiableAt_id
    exact ((hρ.differentiable one_ne_zero) _).comp x h1
  have hui : ∀ i, DifferentiableAt ℝ (fun y => u t y i) x := fun i =>
    ((contDiff_pi.1 (hu t) i).differentiable one_ne_zero) x
  have hprod : ∀ i, partialDeriv i (fun y => (ρ t y • u t y) i) x =
      ρ t x * partialDeriv i (fun y => u t y i) x + u t x i * partialDeriv i (ρ t) x := by
    intro i
    unfold partialDeriv
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [fderiv_fun_mul hρt (hui i)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hm := mass t x
  have hi := incompressible t x
  unfold div at hm ⊢
  simp_rw [hprod, Finset.sum_add_distrib, ← Finset.mul_sum] at hm
  have : ρ t x * ∑ i, partialDeriv i (fun y => u t y i) x = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hpos t x).ne'
  · exact h
