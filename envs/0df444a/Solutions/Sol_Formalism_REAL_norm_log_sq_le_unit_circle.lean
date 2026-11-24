-- Prove2me | solution 1 for Formalism.REAL.norm_log_sq_le_unit_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:59:59.406241+00:00
-- url     : https://prove2.me/submissions/0f000615-d699-4192-9b46-b15f664a6cd8

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactExponentialSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (z : ℂ) (hz : ‖z‖ = 1) : ‖Complex.log z‖ ^ 2 ≤ 3 * ‖z - 1‖ ^ 2 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  set θ := Complex.arg z with hθ
  have hre : z.re = Real.cos θ := by rw [Complex.cos_arg hz0, hz, div_one]
  have him : z.im = Real.sin θ := by rw [Complex.sin_arg, hz, div_one]
  have hlog : ‖Complex.log z‖ ^ 2 = θ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.log_re, Complex.log_im, hz, Real.log_one]
    ring
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_sq_add_sin_sq (θ / 2)
    have h2 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    linarith
  have hsub : ‖z - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hre, him]
    linear_combination Real.cos_sq_add_sin_sq θ - 2 * hc
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ Real.pi / 2 → 4 * y ^ 2 ≤ 12 * Real.sin y ^ 2 := by
    intro y hy0 hy1
    have hs := Real.mul_le_sin hy0 hy1
    have hpi0 := Real.pi_pos
    have hpi : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2]
    have ha0 : 0 ≤ 2 / Real.pi * y := by positivity
    have h1 : (2 / Real.pi * y) ^ 2 ≤ Real.sin y ^ 2 := pow_le_pow_left₀ ha0 hs 2
    have h2 : 4 * y ^ 2 = Real.pi ^ 2 * (2 / Real.pi * y) ^ 2 := by
      field_simp
      ring
    rw [h2]
    nlinarith [sq_nonneg (2 / Real.pi * y)]
  have hb : |θ| ≤ Real.pi := abs_le.2 ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  rw [hlog, hsub]
  rcases le_or_gt 0 θ with h | h
  · have := key (θ / 2) (by linarith) (by rw [abs_of_nonneg h] at hb; linarith)
    nlinarith
  · have := key (-(θ / 2)) (by linarith) (by rw [abs_of_neg h] at hb; linarith)
    rw [Real.sin_neg, neg_sq, neg_sq] at this
    nlinarith
end Formalism.REAL
