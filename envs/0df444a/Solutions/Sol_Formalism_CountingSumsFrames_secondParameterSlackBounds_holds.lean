-- Prove2me | solution 1 for Formalism.CountingSumsFrames.secondParameterSlackBounds_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:14.51814+00:00
-- url     : https://prove2.me/submissions/45165755-5657-43b0-ba8b-bb8363b70f21

import Definitions.Def_Formalism_PolynomialDimension_StatementNum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SecondParameterSlackBoundsHolds
import Theorems.Thm_Formalism_CountingSumsFrames_slack_ge_half
import Theorems.Thm_Formalism_CountingSumsFrames_slackBound_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CountingSumsFrames
open Real
namespace Formalism.CountingSumsFrames
theorem _root_.solution : ParamsII5 := by
  intro CE C₂ _ _
  refine ⟨100, by norm_num, ?_⟩
  intro p r N N₁ Nₛ J k n' L₁ G' Y a c₀ c'' D cStar h
  obtain ⟨hp, hr, hrN1, hN1sq, hrY, hk1, hk2, hL, hD, hcS, ha, hL1, hL1G, hNs1, hNs2, hJ, hJr⟩ := h
  have hN2 : 2 ≤ N := by
    calc 2 ≤ r := hr
      _ = 1 * r := (one_mul _).symm
      _ ≤ J * r := Nat.mul_le_mul_right _ hJ
      _ ≤ N := hJr
  have hrk : r ≤ k := by omega
  have hk8 : 8 ≤ k := by omega
  have hpR : (13 : ℝ) ≤ p := by exact_mod_cast hp
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hrkR : (r : ℝ) ≤ k := by exact_mod_cast hrk
  have hkR : (8 : ℝ) ≤ k := by exact_mod_cast hk8
  have hN1rkR : (N₁ : ℝ) + r ≤ k := by exact_mod_cast (by omega : N₁ + r ≤ k)
  have hJrR : (J : ℝ) * r ≤ N := by exact_mod_cast hJr
  have hcSR : 8 * ((D : ℝ) + 1) ≤ cStar := by exact_mod_cast hcS
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hc00 : (0 : ℝ) ≤ c₀ := by positivity
  have hY : (2 : ℝ) ≤ Y := le_trans hrR hrY
  have hY0 : 0 < Y := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, QII p G' = Q := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', cPrII r N n' c₀ c'' cStar = c' := ⟨_, rfl⟩
  rw [hQ, hc'] at ha
  rw [hQ, hc']
  have hQp : (p : ℝ) ≤ Q := by
    rw [← hQ, QII]
    calc (p : ℝ) = (p : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (p : ℝ) ^ G' := pow_le_pow_right₀ hp1.le (by omega)
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ0 : (0 : ℝ) < Q := by linarith
  have hc'ge : (cStar : ℝ) + r * N * c₀ ≤ c' := by
    rw [← hc', cPrII, omII]
    have : (0 : ℝ) ≤ 2 * r * n' * c'' := by positivity
    linarith
  have hrNc : (0 : ℝ) ≤ r * N * c₀ := by positivity
  have hc0c : (c₀ : ℝ) ≤ c' := by
    have h1 : (1 : ℝ) ≤ r * N := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have h2 : (c₀ : ℝ) ≤ r * N * c₀ := le_mul_of_one_le_left hc00 h1
    linarith
  have hc'8 : (8 : ℝ) ≤ c' := by linarith
  have hk0 : (0 : ℝ) < k := by linarith
  have hM : 0 < Y * (k : ℝ) ^ 2 := by positivity
  have hM1 : (1 : ℝ) ≤ Y * (k : ℝ) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
  have hbig : 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) ≤ a := by
    have h1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 * N * Q ^ 3 := by
      have e1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      have e2 : (1 : ℝ) ≤ Q ^ 3 := one_le_pow₀ hQ1
      have e3 : (1 : ℝ) ≤ N := by linarith
      have e4 : (1 : ℝ) ≤ (r : ℝ) ^ 2 * N := one_le_mul_of_one_le_of_one_le e1 e3
      exact one_le_mul_of_one_le_of_one_le e4 e2
    have h2 : (0 : ℝ) ≤ 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by positivity
    calc 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)
        ≤ 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) * ((r : ℝ) ^ 2 * N * Q ^ 3) :=
          le_mul_of_one_le_right h2 h1
      _ = 100 * (k : ℝ) ^ 3 * (r : ℝ) ^ 2 * N * Q ^ 5 * c' * Y := by ring
      _ ≤ a := ha
  have hkc : (1 : ℝ) ≤ k * c' := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hQQ : (1 : ℝ) ≤ Q ^ 2 := one_le_pow₀ hQ1
  have h2M : 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) ≤ a := by
    calc 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) ≤ 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) * (50 * (k * c')) :=
          le_mul_of_one_le_right (by positivity) (by linarith)
      _ = 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by ring
      _ ≤ a := hbig
  have hpa : (p : ℝ) ≤ a := by
    have e1 : Q ≤ Q * Q := le_mul_of_one_le_right hQ0.le hQ1
    have e2 : Q * Q ≤ 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    linarith
  have ha0 : 0 < a := by linarith
  have hka : (k : ℝ) ≤ a := by
    have e1 : (1 : ℝ) ≤ c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hQQ) hM1
    calc (k : ℝ) ≤ k * (100 * (c' * Q ^ 2 * (Y * (k : ℝ) ^ 2))) :=
          le_mul_of_one_le_right hk0.le (by linarith)
      _ = 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by ring
      _ ≤ a := hbig
  have hPa : (p : ℝ) ^ (L₁ - 1) ≤ (p : ℝ) ^ L₁ := pow_le_pow_right₀ hp1.le (by omega)
  have hPb : (p : ℝ) ^ (L₁ - 1) ≤ (p : ℝ) ^ (L₁ + 1) := pow_le_pow_right₀ hp1.le (by omega)
  have h48 : 16 * 3 * (Y * (k : ℝ) ^ 2) ≤ (p : ℝ) ^ L₁ := by
    have e : (1 : ℝ) ≤ N * Y := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have e1 : Y * (k : ℝ) ^ 2 ≤ Y * (k : ℝ) ^ 2 * (N * Y) := le_mul_of_one_le_right hM.le e
    have e2 : 256 * (k : ℝ) ^ 2 * N * Y ^ 2 = 256 * (Y * (k : ℝ) ^ 2 * (N * Y)) := by ring
    linarith
  have h48r : 16 * (3 * r) * (Y * (k : ℝ) ^ 2) ≤ (p : ℝ) ^ (L₁ + 1) := by
    have e1 : (r : ℝ) * (Y * (k : ℝ) ^ 2) ≤ Y * (Y * (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hrY hM.le
    have e0 : 0 ≤ Y * (Y * (k : ℝ) ^ 2) := by positivity
    have e2 : Y * (Y * (k : ℝ) ^ 2) ≤ Y * (Y * (k : ℝ) ^ 2) * N :=
      le_mul_of_one_le_right e0 (by linarith)
    have e3 : 256 * (k : ℝ) ^ 2 * N * Y ^ 2 = 256 * (Y * (Y * (k : ℝ) ^ 2) * N) := by ring
    linarith
  have hdivX : ∀ X : ℝ, 0 < X → X ≤ Q * Q → 2 * (Y * (k : ℝ) ^ 2) ≤ a / X := by
    intro X hX0 hXQ
    rw [le_div_iff₀ hX0]
    have : 2 * (Y * (k : ℝ) ^ 2) * X ≤ 2 * (Y * (k : ℝ) ^ 2) * (Q * Q) :=
      mul_le_mul_of_nonneg_left hXQ (by positivity)
    linarith
  have hQQQ : Q ≤ Q * Q := le_mul_of_one_le_right hQ0.le hQ1
  have h24 : 24 * k * c' ≤ a / Q / (Y * (k : ℝ) ^ 2) / 2 := by
    rw [div_div, div_div, le_div_iff₀ (by positivity)]
    have e0 : (0 : ℝ) ≤ 24 * k * c' * (Q * (Y * (k : ℝ) ^ 2) * 2) := by positivity
    have e1 := le_mul_of_one_le_right e0 hQ1
    have e2 : 24 * k * c' * (Q * (Y * (k : ℝ) ^ 2) * 2) * Q
        = 48 * (k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)) := by ring
    have e3 : (0 : ℝ) ≤ k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2) := by positivity
    have e4 : 100 * k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)
        = 100 * (k * c' * Q ^ 2 * (Y * (k : ℝ) ^ 2)) := by ring
    linarith
  have hslQ : ∀ B : ℝ, a / Q ≤ B → 24 * k * c' ≤ slII Y k B := by
    intro B hB
    have e1 := slack_ge_half hM (le_trans (hdivX Q hQ0 hQQQ) hB)
    have e2 : a / Q / (Y * (k : ℝ) ^ 2) / 2 ≤ B / (Y * (k : ℝ) ^ 2) / 2 := by gcongr
    linarith
  obtain ⟨lA, hlA⟩ : ∃ x, Real.logb p a = x := ⟨_, rfl⟩
  rw [hlA] at hD
  have hlA1 : 1 ≤ lA := by
    rw [← hlA, ← Real.logb_self_eq_one hp1]
    exact Real.logb_le_logb_of_le hp1 (by linarith) hpa
  obtain ⟨lg, hlg⟩ : ∃ x, lgII p a k = x := ⟨_, rfl⟩
  have hlg0 : 0 ≤ lg := by
    rw [← hlg, lgII]
    have : 0 ≤ Real.logb p (2 * a + k) := Real.logb_nonneg hp1 (by linarith)
    linarith
  have hlg3 : lg ≤ 3 * lA := by
    rw [← hlg, lgII]
    have e1 : Real.logb p (2 * a + k) ≤ Real.logb p (p * a) := by
      apply Real.logb_le_logb_of_le hp1 (by linarith)
      have : 13 * a ≤ p * a := mul_le_mul_of_nonneg_right hpR ha0.le
      linarith
    have e2 : Real.logb p (p * a) = 1 + lA := by
      rw [Real.logb_mul (by linarith) ha0.ne', Real.logb_self_eq_one hp1, hlA]
    linarith
  have hNk0 : (0 : ℝ) ≤ N * (k : ℝ) ^ 2 := by positivity
  have hD1 : degreeLoss p a k N r J ≤ 15 * (N * (k : ℝ) ^ 2 * lA) := by
    have e : degreeLoss p a k N r J
        = lg * (N * (k : ℝ) ^ 2 + 2 * (N * (r : ℝ) ^ 2) + J * r * (r : ℝ) ^ 2 + N * (2 * k)) := by
      rw [degreeLoss, hlg]; ring
    have f1 : (r : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := pow_le_pow_left₀ (by linarith) hrkR 2
    have f2 : (N : ℝ) * (r : ℝ) ^ 2 ≤ N * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left f1 (by linarith)
    have f3 : (J : ℝ) * r * (r : ℝ) ^ 2 ≤ N * (k : ℝ) ^ 2 :=
      mul_le_mul hJrR f1 (by positivity) (by linarith)
    have f4 : (2 : ℝ) * k ≤ (k : ℝ) ^ 2 := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_right (by linarith) hk0.le
    have f5 : (N : ℝ) * (2 * k) ≤ N * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_left f4 (by linarith)
    have f6 : lg * (N * (k : ℝ) ^ 2 + 2 * (N * (r : ℝ) ^ 2) + J * r * (r : ℝ) ^ 2 + N * (2 * k))
        ≤ lg * (5 * (N * (k : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left (by linarith) hlg0
    have f7 : lg * (5 * (N * (k : ℝ) ^ 2)) ≤ 3 * lA * (5 * (N * (k : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right hlg3 (by positivity)
    rw [e]
    calc _ ≤ _ := f6
      _ ≤ _ := f7
      _ = 15 * (N * (k : ℝ) ^ 2 * lA) := by ring
  have hk1' : kappaSecondRegime p a k N ≤ 3 * (N * (k : ℝ) ^ 2 * lA) := by
    rw [kappaSecondRegime, hlg]
    calc (N : ℝ) * (k : ℝ) ^ 2 * lg ≤ N * (k : ℝ) ^ 2 * (3 * lA) := mul_le_mul_of_nonneg_left hlg3 hNk0
      _ = 3 * (N * (k : ℝ) ^ 2 * lA) := by ring
  have hXl : 0 ≤ N * (k : ℝ) ^ 2 * lA := mul_nonneg hNk0 (by linarith)
  have hD' : 100 * (N * (k : ℝ) ^ 2 * lA) ≤ D := by
    have e : 100 * (N * (k : ℝ) ^ 2 * lA) = 100 * N * (k : ℝ) ^ 2 * lA := by ring
    rw [e]; exact hD
  have hkap0 : 0 ≤ kappaSecondRegime p a k N := by
    rw [kappaSecondRegime, hlg]; exact mul_nonneg hNk0 hlg0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Q' B dw hQ'1 hQ'Q hdw hB
    have hz : (p : ℝ) ^ (-(L₁ : ℤ)) = ((p : ℝ) ^ L₁)⁻¹ := by rw [zpow_neg, zpow_natCast]
    rw [hz]
    have hPL : 0 < (p : ℝ) ^ L₁ := by positivity
    have hPL1 : 1 ≤ (p : ℝ) ^ L₁ := one_le_pow₀ hp1.le
    have hQ'0 : 0 < Q' := by linarith
    have haQ' : 2 * (Y * (k : ℝ) ^ 2) ≤ a / Q' := hdivX Q' hQ'0 (le_trans hQ'Q hQQQ)
    have haQ'0 : 0 ≤ a / Q' := by positivity
    have hB1 : a / Q' ≤ B := by
      have e1 : a / Q' ≤ (p : ℝ) ^ L₁ * (a / Q') := le_mul_of_one_le_left haQ'0 hPL1
      have e2 : (p : ℝ) ^ L₁ * a / Q' = (p : ℝ) ^ L₁ * (a / Q') := mul_div_assoc _ _ _
      linarith
    constructor
    · calc dw ≤ 3 * a / Q' := hdw
        _ = 3 * ((p : ℝ) ^ L₁)⁻¹ * ((p : ℝ) ^ L₁ * a / Q') := by field_simp
        _ ≤ 3 * ((p : ℝ) ^ L₁)⁻¹ * B := mul_le_mul_of_nonneg_left hB (by positivity)
    · have e1 := slack_ge_half hM (le_trans haQ' hB1)
      have e2 := slackBound_coeff (c := 3) (B := B) hM (by norm_num) (by linarith) h48
      linarith
  · intro Dd Qj dj B hDd hQj1 hQjQ hdj hB
    have hz1 : (p : ℝ) ^ (-(L₁ : ℤ) - 1) = ((p : ℝ) ^ (L₁ + 1))⁻¹ := by
      rw [show -(L₁ : ℤ) - 1 = -((L₁ + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    have hz2 : (p : ℝ) ^ (-(Dd : ℤ) - L₁ - 1) = ((p : ℝ) ^ Dd * (p : ℝ) ^ (L₁ + 1))⁻¹ := by
      rw [show -(Dd : ℤ) - L₁ - 1 = -((Dd + (L₁ + 1) : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast, pow_add]
    rw [hz2] at hdj
    rw [hz1]
    have hPD : 0 < (p : ℝ) ^ Dd := by positivity
    have hP1 : 0 < (p : ℝ) ^ (L₁ + 1) := by positivity
    have hQj0 : 0 < Qj := by linarith
    have hX : (p : ℝ) ^ Dd * Qj ≤ Q * Q := mul_le_mul hDd hQjQ hQj0.le hQ0.le
    have haX : 2 * (Y * (k : ℝ) ^ 2) ≤ a / ((p : ℝ) ^ Dd * Qj) := hdivX _ (by positivity) hX
    have hr0 : (0 : ℝ) < r := by linarith
    constructor
    · calc (r : ℝ) * dj / Qj ≤ r * (3 * a * ((p : ℝ) ^ Dd * (p : ℝ) ^ (L₁ + 1))⁻¹) / Qj :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdj hr0.le) hQj0.le
        _ = 3 * r * ((p : ℝ) ^ (L₁ + 1))⁻¹ * (a / ((p : ℝ) ^ Dd * Qj)) := by field_simp
        _ ≤ 3 * r * ((p : ℝ) ^ (L₁ + 1))⁻¹ * B := mul_le_mul_of_nonneg_left hB (by positivity)
    · have e1 := slack_ge_half hM (le_trans haX hB)
      have e2 := slackBound_coeff (c := 3 * r) (B := B) hM (by positivity) (by linarith) h48r
      linarith
  · linarith
  · intro B ms hB
    have e1 := hslQ B hB
    have e2 : 2 * c' ≤ k * c' := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · intro B hB
    have e1 := hslQ B hB
    have e2 : ((N₁ : ℝ) + r) * c₀ ≤ k * c' := mul_le_mul hN1rkR hc0c hc00 hk0.le
    linarith
  · linarith
  · linarith
end Formalism.CountingSumsFrames
