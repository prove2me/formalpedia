-- Prove2me | solution 1 for Formalism.DivisionValues.passage_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:45.562819+00:00
-- url     : https://prove2.me/submissions/6c87f6e4-3f68-444c-93a1-b5cafa989e92

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_PassageScaleFree
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : PassageArith := by
  intro muC mu0 HH0 lam0 logκ de c1 c2 c3 Cd f r g k b p1 p2 C0 hc1 hc2 hCd hf hr hk hb hde hg
    hl0 hlb hmu hHH hA hB hcmp hc3
  have hb0 : 0 ≤ b := by linarith
  have hkb : 1 ≤ k * b := by nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 hb)]
  have hkb0 : 0 ≤ k * b := by linarith
  have h8 : 1 ≤ (k * b) ^ 8 := one_le_pow₀ hkb
  have hg0 : 0 < g := by linarith
  have hfr : 0 ≤ Cd * f * r := mul_nonneg (mul_nonneg hCd hf) hr
  have hde0 : 0 ≤ de := by
    rw [hde]
    exact div_nonneg hfr hg0.le
  have hde3 : de ≤ 1 / 3 := by
    rw [hde, div_le_iff₀ hg0]
    linarith
  have hQ : mu0 + HH0 + c2 * lam0 ≤ (p1 + p2 + c2) * b := by
    have := mul_le_mul_of_nonneg_left hlb hc2
    linarith
  have hN : c1 * Cd * f * r * (p1 + p2 + c2) * b ≤ (k * b) ^ 8 := by
    have h1 := mul_le_mul_of_nonneg_right hA hb0
    have h2 : (k * b) ^ 7 * b ≤ (k * b) ^ 7 * (k * b) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (sub_nonneg.2 hk) hb0]) (pow_nonneg hkb0 7)
    have h3 : (k * b) ^ 7 * (k * b) = (k * b) ^ 8 := by ring
    linarith
  have hd1 : c1 * de * (mu0 + HH0 + c2 * lam0) ≤ 1 := by
    have hc1de : 0 ≤ c1 * de := mul_nonneg hc1 hde0
    have h1 : c1 * de * (mu0 + HH0 + c2 * lam0) ≤ c1 * de * ((p1 + p2 + c2) * b) :=
      mul_le_mul_of_nonneg_left hQ hc1de
    have h2 : c1 * de * ((p1 + p2 + c2) * b) = c1 * Cd * f * r * (p1 + p2 + c2) * b / g := by
      rw [hde]
      ring
    have h3 : c1 * Cd * f * r * (p1 + p2 + c2) * b / g ≤ 1 := by
      rw [div_le_one hg0]
      linarith
    linarith
  have hc3l : c3 * lam0 ≤ C0 * lam0 := mul_le_mul_of_nonneg_right hc3 hl0
  refine ⟨hde0, hde3, by linarith [hcmp hde3], hd1, by linarith⟩
end Formalism.DivisionValues
