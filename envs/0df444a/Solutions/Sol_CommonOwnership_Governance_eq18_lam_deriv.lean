-- Prove2me | solution 1 for CommonOwnership.Governance.eq18_lam_deriv
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:17:05.518562+00:00
-- url     : https://prove2.me/submissions/fdf4c307-f1a3-43c8-8db3-e39c42adc32c

import Mathlib
import Definitions.Def_CommonOwnership_Governance_Model
set_option autoImplicit false
open CommonOwnership.Governance

theorem solution (θ β s : ℝ) (hθ : 0 < θ) (hβ : 0 < β) :
    HasDerivAt (fun x => lam θ β x)
      (2 * θ * s * β * (β - s) / ((β - s) ^ 2 + θ * s ^ 2) ^ 2) s := by
  have hD : (β - s) ^ 2 + θ * s ^ 2 ≠ 0 := by
    by_cases h : s = 0
    · subst h
      simp
      exact hβ.ne'
    · have : 0 < θ * s ^ 2 := by positivity
      nlinarith [sq_nonneg (β - s)]
  have hnum : HasDerivAt (fun x : ℝ => θ * x ^ 2) (θ * (2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_mul θ
  have h1 : HasDerivAt (fun x : ℝ => β - x) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub β
  have hden : HasDerivAt (fun x : ℝ => (β - x) ^ 2 + θ * x ^ 2)
      (2 * (β - s) * (-1) + θ * (2 * s)) s := by
    refine ((h1.pow 2).add hnum).congr_deriv ?_
    simp
  have := hnum.div hden hD
  refine this.congr_deriv ?_
  field_simp
  ring

