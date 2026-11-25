-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.normal_form_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:44:30.221689+00:00
-- url     : https://prove2.me/submissions/b9ed8c0f-21f6-40f6-966c-b8b65a876b99

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DbarConjugationWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.NFWeight := by
  intro N i i' D Gv c hD hG hc hii
  have hd : 0 < ‖D‖ := norm_pos_iff.2 hD
  have h1 : ‖D ^ i * (starRingEnd ℂ) D ^ i'‖ = (‖D‖ ^ N)⁻¹ := by
    rw [norm_mul, norm_zpow, norm_zpow, Complex.norm_conj, ← zpow_add₀ hd.ne', hii, zpow_neg, zpow_natCast]
  have hGN : 0 < Gv ^ ((N : ℝ) / 2) := Real.rpow_pos_of_pos hG _
  have key : (Complex.normSq D / Gv) ^ N * c = (‖D‖ ^ N * (Gv ^ ((N : ℝ) / 2))⁻¹) ^ 2 * c := by
    have e : (Gv ^ ((N : ℝ) / 2)) ^ 2 = Gv ^ N := by
      rw [← Real.rpow_natCast (Gv ^ ((N : ℝ) / 2)) 2, ← Real.rpow_mul hG.le]
      norm_num
    rw [mul_pow, inv_pow, e, Complex.normSq_eq_norm_sq, div_pow, ← pow_mul, ← pow_mul, mul_comm 2 N]
    ring
  rw [key, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), h1, neg_div, Real.rpow_neg hG.le]
  field_simp
end Formalism.FourierDecayAlt.P
