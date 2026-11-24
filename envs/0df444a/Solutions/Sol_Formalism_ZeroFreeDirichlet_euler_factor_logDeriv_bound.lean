-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.euler_factor_logDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:07.660149+00:00
-- url     : https://prove2.me/submissions/bda6d851-0db5-4972-ace4-f664fbd7e5b8

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_EulerFactorLogDerivBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 ∧ DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ∧
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hw : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  have hx : (p : ℝ) ^ (-s.re) ≤ 1 / 2 := by
    have h1 : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    have h2 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have hx0 : 0 ≤ (p : ℝ) ^ (-s.re) := Real.rpow_nonneg (by linarith) _
  have hden : 1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one, hw] at this
    linarith
  have hne : (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have hder : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      ((p : ℂ) ^ (-s) * Complex.log p) s := by
    have h1 : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
      (hasDerivAt_id s).neg.const_cpow (Or.inl hp0)
    have h2 := (hasDerivAt_const s (1 : ℂ)).sub h1
    exact h2.congr_deriv (by ring)
  refine ⟨hne, hder.differentiableAt, ?_⟩
  have hL : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := Complex.natCast_log.symm
  rw [logDeriv_apply, hder.deriv, norm_div, norm_mul, hw, hlog, Complex.norm_of_nonneg hL]
  have hdpos : 0 < ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  rw [div_le_iff₀ hdpos]
  have hxd : (p : ℝ) ^ (-s.re) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hxd hL]
end Formalism.ZeroFreeDirichlet
