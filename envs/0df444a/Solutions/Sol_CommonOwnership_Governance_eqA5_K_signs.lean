-- Prove2me | solution 1 for CommonOwnership.Governance.eqA5_K_signs
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:17:34.970112+00:00
-- url     : https://prove2.me/submissions/c6ff81a1-4464-4428-9d67-2c94d0b6b4c8

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
set_option autoImplicit false
open CommonOwnership.Governance

theorem solution (β ξ γ sp Pi0 Pip : ℝ) (hβ : 0 < β) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hγ : 0 < γ) (hPip : 0 < Pip) (hgain : Pi0 < Pip) :
    deriv (fun x => Kfun β x γ sp Pi0 Pip) ξ < 0 ∧
      0 < deriv (fun y => Kfun β ξ y sp Pi0 Pip) γ := by
  have hr : 0 < (Pip - Pi0) / Pip := div_pos (by linarith) hPip
  constructor
  · have h1 : HasDerivAt (fun x : ℝ => 2 * γ * β * (1 - x)) (2 * γ * β * (-1)) ξ := by
      simpa using ((hasDerivAt_id ξ).const_sub 1).const_mul (2 * γ * β)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * ξ) ξ := by
      simpa using hasDerivAt_pow 2 ξ
    have h3 := h1.div h2 (by positivity)
    have h4 := (((h3.add_const (β ^ 2)).mul_const ((Pip - Pi0) / Pip)).sub_const (sp ^ 2))
    have h5 : deriv (fun x => Kfun β x γ sp Pi0 Pip) ξ = _ := h4.deriv
    rw [h5]
    have hnum : 2 * γ * β * (-1) * ξ ^ 2 - 2 * γ * β * (1 - ξ) * (2 * ξ)
        = -(2 * γ * β * ξ * (2 - ξ)) := by ring
    simp only [hnum]
    have : 0 < 2 * γ * β * ξ * (2 - ξ) :=
      mul_pos (mul_pos (mul_pos (mul_pos two_pos hγ) hβ) hξ) (by linarith)
    have h6 : -(2 * γ * β * ξ * (2 - ξ)) / (ξ ^ 2) ^ 2 < 0 :=
      div_neg_of_neg_of_pos (by linarith) (by positivity)
    exact mul_neg_of_neg_of_pos h6 hr
  · have h1 : HasDerivAt (fun y : ℝ => 2 * y * β * (1 - ξ)) (2 * 1 * β * (1 - ξ)) γ :=
      ((((hasDerivAt_id γ).const_mul 2).mul_const β)).mul_const (1 - ξ)
    have h3 := h1.div_const (ξ ^ 2)
    have h4 := (((h3.add_const (β ^ 2)).mul_const ((Pip - Pi0) / Pip)).sub_const (sp ^ 2))
    have h5 : deriv (fun y => Kfun β ξ y sp Pi0 Pip) γ = _ := h4.deriv
    rw [h5]
    have : 0 < 2 * 1 * β * (1 - ξ) / ξ ^ 2 := by
      have : 0 < 1 - ξ := by linarith
      positivity
    exact mul_pos this hr

