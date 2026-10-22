-- Prove2me | solution 1 for CommonOwnership.Governance.eqA2_dS
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:25:59.744233+00:00
-- url     : https://prove2.me/submissions/df444df9-1e7f-4f63-a083-689d119748f4

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
set_option autoImplicit false
open CommonOwnership.Governance

theorem solution (β ξ γ s : ℝ) (hξ : 0 < ξ) (hγ : 0 < γ) (Pi_ : ℝ → ℝ) (d : ℝ)
    (hd : HasDerivAt Pi_ d s) (hPi : Pi_ s ≠ 0) :
    HasDerivAt (surplusQ β ξ γ Pi_) (ξ ^ 2 / γ * Hfun β ξ γ s (d / Pi_ s) * Pi_ s) s := by
  have hnu : ∀ t, nuStar (quadCost γ) (fun t => ξ * t / γ) β ξ t
      = β * (1 - ξ) + ξ ^ 2 / (2 * γ) * (β ^ 2 - t ^ 2) := by
    intro t; unfold nuStar quadCost; field_simp; ring
  have hfun : surplusQ β ξ γ Pi_
      = fun t => (β * (1 - ξ) + ξ ^ 2 / (2 * γ) * (β ^ 2 - t ^ 2)) * Pi_ t := by
    funext t; unfold surplusQ; rw [hnu]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => β * (1 - ξ) + ξ ^ 2 / (2 * γ) * (β ^ 2 - t ^ 2))
      (-(ξ ^ 2 / γ) * s) s := by
    have := (((hasDerivAt_pow 2 s).const_sub (β ^ 2)).const_mul (ξ ^ 2 / (2 * γ))).const_add
      (β * (1 - ξ))
    refine this.congr_deriv ?_
    push_cast
    field_simp
  have h2 := h1.mul hd
  refine h2.congr_deriv ?_
  unfold Hfun
  field_simp
