-- Prove2me | solution 1 for FoundationsRL.GeneralDM.lemma20_bounded_likelihood_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T20:22:54.685443+00:00
-- url     : https://prove2.me/submissions/066b2519-4592-412e-be1a-9087757cb2f3

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

set_option autoImplicit false

namespace P14807859

/-- For `0 < a < b`: `log (b / a) * (a + b) ≥ 2 (b - a)`. -/
lemma log_lower (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    2 * (b - a) ≤ Real.log (b / a) * (a + b) := by
  have hc : 0 < a / (b - a) := div_pos ha (by linarith)
  have hs := Real.hasSum_log_one_add_inv hc
  have h1 : (1 : ℝ) + (a / (b - a))⁻¹ = b / a := by
    rw [inv_div]; field_simp; ring
  rw [h1] at hs
  have hle := le_hasSum hs 0 (fun j _ => by positivity)
  simp only [Nat.cast_zero, mul_zero, zero_add, div_one, pow_one, mul_one] at hle
  have h2 : (1 : ℝ) / (2 * (a / (b - a)) + 1) = (b - a) / (a + b) := by
    have : b - a ≠ 0 := by linarith
    field_simp; ring
  rw [h2] at hle
  have hab' : 0 < a + b := by linarith
  rw [mul_div_assoc', div_le_iff₀ hab'] at hle
  linarith

lemma pw (p q V : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hV : 1 ≤ V) (h : p ≤ V * q) :
    p * Real.log (p / q) - p + q ≤ (2 + Real.log V) * (Real.sqrt p - Real.sqrt q) ^ 2 := by
  have hlV : 0 ≤ Real.log V := Real.log_nonneg hV
  rcases hq.eq_or_lt with hq0 | hqpos
  · subst hq0
    have : p = 0 := by nlinarith
    subst this; simp
  rcases hp.eq_or_lt with hp0 | hppos
  · subst hp0
    simp only [zero_mul, Real.sqrt_zero, zero_sub, neg_sq, Real.sq_sqrt hq]
    nlinarith
  set a := Real.sqrt p with ha_def
  set b := Real.sqrt q with hb_def
  have ha : 0 < a := Real.sqrt_pos.mpr hppos
  have hb : 0 < b := Real.sqrt_pos.mpr hqpos
  have hpa : p = a ^ 2 := (Real.sq_sqrt hp).symm
  have hqb : q = b ^ 2 := (Real.sq_sqrt hq).symm
  have hlog : Real.log (p / q) = 2 * Real.log (a / b) := by
    rw [hpa, hqb, ← div_pow, Real.log_pow]; norm_num
  rw [hlog, hpa, hqb]
  set L := Real.log (a / b) with hL
  rcases le_or_gt a b with hab | hab
  · -- a ≤ b
    have key : L * (a + b) ≤ 2 * (a - b) := by
      rcases hab.eq_or_lt with h' | h'
      · rw [hL, h', div_self hb.ne']; simp
      · have := log_lower a b ha h'
        have e : Real.log (b / a) = -L := by
          rw [hL, ← Real.log_inv, inv_div]
        rw [e] at this; linarith
    have hpos : 0 < a + b := by linarith
    have h2 : (a ^ 2 * (2 * L) - a ^ 2 + b ^ 2) ≤ 2 * (a - b) ^ 2 := by
      have : (a ^ 2 * (2 * L) - a ^ 2 + b ^ 2) * (a + b) ≤ 2 * (a - b) ^ 2 * (a + b) := by
        have h3 : 0 ≤ (b - a) ^ 3 := by have : 0 ≤ b - a := by linarith
                                        positivity
        nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg a)]
      exact le_of_mul_le_mul_right this hpos
    nlinarith [sq_nonneg (a - b)]
  · -- a > b
    have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hb]; linarith)
    have hsinh : L ≤ ((a / b) - (a / b)⁻¹) / 2 := by
      rw [← Real.sinh_log (div_pos ha hb)]
      exact Real.self_le_sinh_iff.mpr hL0
    have key : 2 * a * b * L ≤ a ^ 2 - b ^ 2 := by
      rw [inv_div] at hsinh
      have : ((a / b) - (b / a)) / 2 = (a ^ 2 - b ^ 2) / (2 * a * b) := by
        field_simp
      rw [this, le_div_iff₀ (by positivity)] at hsinh
      linarith
    have hLV : 2 * L ≤ Real.log V := by
      have hr : (a / b) ^ 2 ≤ V := by
        rw [div_pow, div_le_iff₀ (by positivity)]; nlinarith
      have := Real.log_le_log (by positivity) hr
      rw [Real.log_pow] at this; push_cast at this; linarith
    have h2 : a ^ 2 * (2 * L) - a ^ 2 + b ^ 2 ≤ (2 + 2 * L) * (a - b) ^ 2 := by
      have : (a ^ 2 * (2 * L) - a ^ 2 + b ^ 2) * a ≤ (2 + 2 * L) * (a - b) ^ 2 * a := by
        have h3 : 0 ≤ (a - b) ^ 3 := by have : 0 ≤ a - b := by linarith
                                        positivity
        have h4 : 0 ≤ 2 * a - b := by linarith
        nlinarith [mul_le_mul_of_nonneg_right key h4]
      exact le_of_mul_le_mul_right this ha
    nlinarith [sq_nonneg (a - b)]

end P14807859

open FoundationsRL.GeneralDM in
theorem solution {Y : Type*} [Fintype Y] (P Q : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1)
    (V : ℝ) (hV : 0 < V)
    (hratio : ∀ F : Finset Y, (∑ y ∈ F, P y) ≤ V * ∑ y ∈ F, Q y) :
    klDivDiscrete P Q ≤ ENNReal.ofReal ((2 + Real.log V) * hellingerSq P Q) := by
  have hpt : ∀ y, P y ≤ V * Q y := fun y => by simpa using hratio {y}
  have hV1 : 1 ≤ V := by
    have := hratio Finset.univ; rw [hP.2, hQ.2] at this; linarith
  have hac : ∀ y, Q y = 0 → P y = 0 := fun y hy =>
    le_antisymm (by simpa [hy] using hpt y) (hP.1 y)
  unfold klDivDiscrete hellingerSq
  rw [if_pos hac]
  apply ENNReal.ofReal_le_ofReal
  have e : ∑ y, P y * Real.log (P y / Q y) = ∑ y, (P y * Real.log (P y / Q y) - P y + Q y) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hP.2, hQ.2]; ring
  rw [e, Finset.mul_sum]
  exact Finset.sum_le_sum fun y _ => P14807859.pw (P y) (Q y) V (hP.1 y) (hQ.1 y) hV1 (hpt y)
