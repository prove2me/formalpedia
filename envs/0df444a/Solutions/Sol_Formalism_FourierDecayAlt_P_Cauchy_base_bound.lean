-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Cauchy.base_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.870947+00:00
-- url     : https://prove2.me/submissions/8338a415-fa05-48d5-bacc-3da3a1577f88

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Cauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Cauchy
open Complex Metric Set
namespace Formalism.FourierDecayAlt.P.Cauchy
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) (u : ℝ) {ρ : ℝ} (hρ : ρ ≤ 1 / 16) {w : ℂ}
    (hw : ‖w - u‖ ≤ ρ) :
    (1 + ε * Real.exp (-u)) * (1 - 2 * ρ) ≤ (1 + (ε : ℂ) * Complex.exp (-w)).re := by
  set a : ℝ := ε * Real.exp (-u) with ha
  have ha0 : 0 < a := by positivity
  have h1 : 1 + (ε : ℂ) * Complex.exp (-w) = ((1 + a : ℝ) : ℂ) + (a : ℂ) * (Complex.exp (-(w - u)) - 1) := by
    have : Complex.exp (-w) = Complex.exp (-(u : ℂ)) * Complex.exp (-(w - u)) := by
      rw [← Complex.exp_add]; congr 1; ring
    rw [this, ha]
    push_cast
    ring
  have h2 : ‖Complex.exp (-(w - u)) - 1‖ ≤ 2 * ρ := by
    have h := Complex.norm_exp_sub_one_le (x := -(w - u)) (by rw [norm_neg]; linarith)
    rw [norm_neg] at h
    linarith
  have h3 : -(2 * ρ) ≤ (Complex.exp (-(w - u)) - 1).re := by
    have := Complex.abs_re_le_norm (Complex.exp (-(w - u)) - 1)
    have := neg_abs_le (Complex.exp (-(w - u)) - 1).re
    linarith
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hw
  have h4 : a * -(2 * ρ) ≤ a * (Complex.exp (-(w - u)) - 1).re :=
    mul_le_mul_of_nonneg_left h3 ha0.le
  rw [h1, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul]
  nlinarith
end Formalism.FourierDecayAlt.P.Cauchy
