-- Prove2me | solution 1 for Formalism.SLP.GlobalBoundRefinements.P.coefficients_of_form_preserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:27.739451+00:00
-- url     : https://prove2.me/submissions/a99b3b8d-3fdc-47b0-b2a2-faf7c4b3334c

import Definitions.Def_Formalism_HyperbolicPlaceProducts_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DetIndexProductHyperbolicInequality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.GlobalBoundRefinements Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements
set_option maxHeartbeats 800000
namespace Formalism.SLP.GlobalBoundRefinements.P
theorem _root_.solution : Formalism.SLP.GlobalBoundRefinements.FormCoeff := by
  intro a b c d T T' hT hT' hform
  have h10 := hform 1 0
  have h01 := hform 0 1
  simp only [mul_one, mul_zero, add_zero, zero_add, norm_one, norm_zero, one_pow] at h10 h01
  norm_num at h10 h01
  have e1 : ‖a‖ ^ 2 - 1 = T' * ‖c‖ ^ 2 / T := by
    field_simp
    linarith
  have e2 : ‖d‖ ^ 2 - 1 = T * ‖b‖ ^ 2 / T' := by
    field_simp
    linarith
  refine ⟨e1, e2, fun ha => ?_⟩
  have hc2 : ‖c‖ ^ 2 = 0 := by
    rw [ha] at h10
    nlinarith [sq_nonneg ‖c‖]
  have hc : c = 0 := by simpa using hc2
  have haa : a * (starRingEnd ℂ a) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have hx := hform (starRingEnd ℂ a * b) 1
  have h2b : a * (starRingEnd ℂ a * b) + b * 1 = 2 * b := by
    rw [← mul_assoc, haa]
    ring
  rw [h2b, hc] at hx
  simp only [zero_mul, zero_add, mul_one, norm_mul, Complex.norm_conj, ha, one_mul, norm_one,
    one_pow] at hx
  norm_num at hx
  have hb2 : ‖b‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖b‖]
  have hb : b = 0 := by simpa using hb2
  refine ⟨hc, hb, ?_⟩
  rw [hb, norm_zero] at e2
  have hd2 : ‖d‖ ^ 2 = 1 := by linarith [e2, show T * (0:ℝ) ^ 2 / T' = 0 by simp]
  nlinarith [norm_nonneg d]
end Formalism.SLP.GlobalBoundRefinements.P
