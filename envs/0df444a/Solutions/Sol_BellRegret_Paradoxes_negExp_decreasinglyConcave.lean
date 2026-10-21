-- Prove2me | solution 1 for BellRegret.Paradoxes.negExp_decreasinglyConcave
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:47:36.076037+00:00
-- url     : https://prove2.me/submissions/8147babd-3c08-4c95-8f7c-640875616ac2

import Mathlib
import Definitions.Def_BellRegret_Paradoxes_Model

set_option autoImplicit false
open BellRegret.Paradoxes

theorem negExp_hasDeriv (γ r : ℝ) :
    HasDerivAt (negExp γ) (γ * Real.exp (-(γ * r))) r := by
  have h1 : HasDerivAt (fun r : ℝ => -(γ * r)) (-γ) r := by
    exact (((hasDerivAt_id' r).const_mul γ).neg).congr_deriv (by ring)
  have h2 := (h1.exp).const_sub 1
  have e : negExp γ = fun r => 1 - Real.exp (-(γ * r)) := by funext y; rfl
  rw [e]
  exact h2.congr_deriv (by ring)

theorem deriv_negExp (γ : ℝ) : deriv (negExp γ) = fun r => γ * Real.exp (-(γ * r)) :=
  funext fun r => (negExp_hasDeriv γ r).deriv

theorem negExp_hasDeriv2 (γ r : ℝ) :
    HasDerivAt (fun r => γ * Real.exp (-(γ * r))) (-(γ * γ * Real.exp (-(γ * r)))) r := by
  have h1 : HasDerivAt (fun r : ℝ => -(γ * r)) (-γ) r := by
    exact (((hasDerivAt_id' r).const_mul γ).neg).congr_deriv (by ring)
  have h2 := h1.exp.const_mul γ
  exact h2.congr_deriv (by ring)

theorem deriv2_negExp (γ : ℝ) :
    deriv (deriv (negExp γ)) = fun r => -(γ * γ * Real.exp (-(γ * r))) := by
  rw [deriv_negExp]
  exact funext fun r => (negExp_hasDeriv2 γ r).deriv

theorem solution (γ : ℝ) (hγ : 0 < γ) :
    DecreasinglyConcave (negExp γ) := by
  refine ⟨fun r => (negExp_hasDeriv γ r).differentiableAt, ?_, ?_⟩
  · rw [deriv_negExp]
    exact fun r => (negExp_hasDeriv2 γ r).differentiableAt
  · rw [deriv2_negExp]
    intro a b hab
    have h1 : Real.exp (-(γ * b)) < Real.exp (-(γ * a)) :=
      Real.exp_lt_exp.2 (by nlinarith)
    have h2 : 0 < γ * γ := mul_pos hγ hγ
    show -(γ * γ * Real.exp (-(γ * a))) < -(γ * γ * Real.exp (-(γ * b)))
    nlinarith
