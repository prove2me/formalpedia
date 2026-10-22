-- Prove2me | solution 1 for CommonOwnership.Governance.eqA3_H_signs
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:17:20.092697+00:00
-- url     : https://prove2.me/submissions/3219b182-8127-4f17-b88e-6857b6a944be

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
set_option autoImplicit false
open CommonOwnership.Governance

theorem solution (β ξ γ s g : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hγ : 0 < γ)
    (hg : 0 < g) :
    deriv (fun x => Hfun β x γ s g) ξ < 0 ∧ 0 < deriv (fun y => Hfun β ξ y s g) γ := by
  constructor
  · have h1 : HasDerivAt (fun x : ℝ => γ * β * (1 - x)) (γ * β * (-1)) ξ := by
      simpa using ((hasDerivAt_id ξ).const_sub 1).const_mul (γ * β)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ξ) ξ := by
      simpa using hasDerivAt_pow 2 ξ
    have h3 := h1.div h2 (by positivity)
    have h4 := ((h3.add_const (1 / 2 * (β ^ 2 - s ^ 2))).mul_const g).const_add (-s)
    have h5 : deriv (fun x => Hfun β x γ s g) ξ = _ := h4.deriv
    rw [h5]
    have hnum : γ * β * (-1) * ξ ^ 2 - γ * β * (1 - ξ) * (2 * ξ) = -(γ * β * ξ * (2 - ξ)) := by
      ring
    simp only [hnum]
    have : 0 < γ * β * ξ * (2 - ξ) := mul_pos (mul_pos (mul_pos hγ hβ) hξ) (by linarith)
    have h6 : -(γ * β * ξ * (2 - ξ)) / (ξ ^ 2) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact mul_neg_of_neg_of_pos h6 hg
  · have h1 : HasDerivAt (fun y : ℝ => y * β * (1 - ξ)) (1 * β * (1 - ξ)) γ :=
      ((hasDerivAt_id γ).mul_const β).mul_const (1 - ξ)
    have h3 := h1.div_const (ξ ^ 2)
    have h4 := ((h3.add_const (1 / 2 * (β ^ 2 - s ^ 2))).mul_const g).const_add (-s)
    have h5 : deriv (fun y => Hfun β ξ y s g) γ = _ := h4.deriv
    rw [h5]
    have : 0 < 1 * β * (1 - ξ) / ξ ^ 2 := by
      have : 0 < 1 - ξ := by linarith
      positivity
    exact mul_pos this hg

