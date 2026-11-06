-- Prove2me | solution 1 for ChoicePAC.MidPoint.midpoint_pac_bounded_loss
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:13:08.37867+00:00
-- url     : https://prove2.me/submissions/4f3566e6-1e0f-40de-b71a-a6af2bd0bb4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions
import Definitions.Def_ChoicePAC_MidPoint_GF
import Theorems.Thm_ChoicePAC_MidPoint_theorem_5_3_general_bound
import Theorems.Thm_ChoicePAC_MidPoint_midpoint_G_bound

open ChoicePAC.MidPoint MeasureTheory

namespace GoalAux

lemma mp_time_eq (k j : ℕ) (hj : j ≤ (midpointSchedule k).M) :
    (midpointSchedule k).time j = 1 - (1 / 2 : ℝ) ^ j := by
  unfold Schedule.time
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · simp
  · have h1 : j - 1 < (midpointSchedule k).M := by omega
    rw [if_neg (by omega), dif_pos h1]
    show 1 - (1 / 2 : ℝ) ^ ((j - 1) + 1) = _
    rw [Nat.sub_add_cancel hpos]

/-- `e^{-x} ≤ 24 / x^4` for `x > 0`. -/
lemma exp_neg_le (x : ℝ) (hx : 0 < x) : Real.exp (-x) ≤ 24 / x ^ 4 := by
  have h := Real.pow_div_factorial_le_exp x hx.le 4
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4] at h
  rw [Real.exp_neg, le_div_iff₀ (by positivity)]
  have hpos := Real.exp_pos x
  rw [inv_mul_eq_div, div_le_iff₀ hpos]
  linarith

/-- The pointwise bound on the integrand of (8) for the mid-point schedule. -/
lemma integrand_bound (k : ℕ) (hk : 1 ≤ k) (c0 ρ' D : ℝ) (hc0 : 0 < c0) (hρ' : 0 < ρ')
    (hD1 : 1 ≤ D) (hD : ρ' * Real.exp (4 * c0 ^ 2) * 24 / c0 ^ 4 ≤ D)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    min 1 (ρ' * (midpointSchedule k).F k (c0 / Real.sqrt (max 1 ((k : ℝ) * (1 - t)))) t) ≤
      2 * D / (1 + ((k : ℝ) - (k : ℝ) * t) ^ 2) := by
  set u : ℝ := (k : ℝ) * (1 - t) with hu
  have hu' : (k : ℝ) - (k : ℝ) * t = u := by rw [hu]; ring
  rw [hu']
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) (by linarith)
  by_cases hcase : t < (midpointSchedule k).time (midpointSchedule k).M ∧ 1 ≤ u
  · obtain ⟨htM, hu1⟩ := hcase
    have hG := midpoint_G_bound k hk t ht0 htM
    rw [max_eq_right hu1]
    set v := c0 / Real.sqrt u with hv
    have hsq : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
    have hv0 : 0 ≤ v := by positivity
    have hv2 : (k : ℝ) * v ^ 2 * (1 - t) = c0 ^ 2 := by
      rw [hv, div_pow, Real.sq_sqrt hu0]
      have : (k : ℝ) * (1 - t) = u := rfl
      field_simp
      linarith
    have hv1 : (k : ℝ) * v * (1 - t) = c0 * Real.sqrt u := by
      rw [hv]
      have : (k : ℝ) * (1 - t) = u := rfl
      have hsu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0
      field_simp
      nlinarith
    have hexp : (k : ℝ) * v ^ 2 * (midpointSchedule k).G t - (k : ℝ) * v * (1 - t) ≤
        4 * c0 ^ 2 + -(c0 * Real.sqrt u) := by
      have : (k : ℝ) * v ^ 2 * (midpointSchedule k).G t ≤ (k : ℝ) * v ^ 2 * (4 * (1 - t)) :=
        mul_le_mul_of_nonneg_left hG (by positivity)
      nlinarith
    have hF : (midpointSchedule k).F k v t ≤ Real.exp (4 * c0 ^ 2) * (24 / (c0 * Real.sqrt u) ^ 4) := by
      unfold Schedule.F
      calc Real.exp ((k : ℝ) * v ^ 2 * (midpointSchedule k).G t - (k : ℝ) * v * (1 - t))
          ≤ Real.exp (4 * c0 ^ 2 + -(c0 * Real.sqrt u)) := Real.exp_le_exp.mpr hexp
        _ = Real.exp (4 * c0 ^ 2) * Real.exp (-(c0 * Real.sqrt u)) := Real.exp_add _ _
        _ ≤ Real.exp (4 * c0 ^ 2) * (24 / (c0 * Real.sqrt u) ^ 4) :=
            mul_le_mul_of_nonneg_left (exp_neg_le _ (by positivity)) (Real.exp_pos _).le
    have hpow : (c0 * Real.sqrt u) ^ 4 = c0 ^ 4 * u ^ 2 := by
      have : Real.sqrt u ^ 4 = (Real.sqrt u ^ 2) ^ 2 := by ring
      rw [mul_pow, this, Real.sq_sqrt hu0]
    rw [hpow] at hF
    have h1 : ρ' * (midpointSchedule k).F k v t ≤ D / u ^ 2 := by
      calc ρ' * (midpointSchedule k).F k v t
          ≤ ρ' * (Real.exp (4 * c0 ^ 2) * (24 / (c0 ^ 4 * u ^ 2))) :=
            mul_le_mul_of_nonneg_left hF hρ'.le
        _ = (ρ' * Real.exp (4 * c0 ^ 2) * 24 / c0 ^ 4) / u ^ 2 := by
            field_simp
        _ ≤ D / u ^ 2 := div_le_div_of_nonneg_right hD (by positivity)
    have h2 : D / u ^ 2 ≤ 2 * D / (1 + u ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 1 + u ^ 2 ≤ 2 * u ^ 2 := by nlinarith
      nlinarith
    exact le_trans (min_le_right _ _) (h1.trans h2)
  · have hule : u ≤ 1 := by
      rw [not_and_or] at hcase
      rcases hcase with h | h
      · push Not at h
        have hM := mp_time_eq k _ le_rfl
        rw [hM] at h
        have hkp : (k : ℝ) ≤ 2 ^ (midpointSchedule k).M := by
          have := Nat.le_pow_clog (by norm_num : 1 < 2) k
          exact_mod_cast this
        have h12 : (1 / 2 : ℝ) ^ (midpointSchedule k).M = 1 / 2 ^ (midpointSchedule k).M := by
          rw [one_div_pow]
        rw [h12] at h
        have hpos : (0 : ℝ) < 2 ^ (midpointSchedule k).M := by positivity
        have : 1 - t ≤ 1 / 2 ^ (midpointSchedule k).M := by linarith
        rw [hu]
        calc (k : ℝ) * (1 - t) ≤ (k : ℝ) * (1 / 2 ^ (midpointSchedule k).M) :=
              mul_le_mul_of_nonneg_left this (by linarith)
          _ ≤ 2 ^ (midpointSchedule k).M * (1 / 2 ^ (midpointSchedule k).M) :=
              mul_le_mul_of_nonneg_right hkp (by positivity)
          _ = 1 := by field_simp
      · linarith
    have : 1 ≤ 2 * D / (1 + u ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    exact le_trans (min_le_left _ _) this

end GoalAux

theorem solution {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ k : ℕ, 1 ≤ k → ∀ sel, I.IsAdmissibleSelector sel →
        I.dlpValue ((k : ℝ) • I.C) ((k : ℝ) • I.lam) - I.pacValue sel k (midpointSchedule k) ≤ ρ := by
  obtain ⟨ρ, ρhat, ρ', hρ, hρhat, hρ', h53⟩ := theorem_5_3_general_bound I hI h21 h22
  set c0 : ℝ := 1 / (1 + |I.ξmax|) with hc0
  have hc0pos : 0 < c0 := by positivity
  have hc0le : c0 ≤ 1 := by
    rw [hc0, div_le_one (by positivity)]; linarith [abs_nonneg I.ξmax]
  have hc0ξ : c0 * I.ξmax ≤ 1 := by
    rw [hc0, one_div_mul_eq_div, div_le_one (by positivity)]
    linarith [le_abs_self I.ξmax]
  set D : ℝ := max 1 (ρ' * Real.exp (4 * c0 ^ 2) * 24 / c0 ^ 4) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  set v : ℕ → ℝ → ℝ := fun k t => c0 / Real.sqrt (max 1 ((k : ℝ) * (1 - t))) with hv
  have hvprop : ∀ k' : ℕ, 1 ≤ k' → ∀ t : ℝ, 0 ≤ t → t < 1 →
      0 < v k' t ∧ v k' t ≤ 1 ∧ v k' t * I.ξmax ≤ 1 := by
    intro k' _ t _ _
    have hs : 1 ≤ Real.sqrt (max 1 ((k' : ℝ) * (1 - t))) := by
      rw [Real.one_le_sqrt]; exact le_max_left _ _
    have hspos : 0 < Real.sqrt (max 1 ((k' : ℝ) * (1 - t))) := by linarith
    have hvle : v k' t ≤ c0 := by
      show c0 / _ ≤ c0
      rw [div_le_iff₀ hspos]; nlinarith
    have hvpos : 0 < v k' t := div_pos hc0pos hspos
    refine ⟨hvpos, hvle.trans hc0le, ?_⟩
    rcases le_or_gt 0 I.ξmax with hx | hx
    · calc v k' t * I.ξmax ≤ c0 * I.ξmax := mul_le_mul_of_nonneg_right hvle hx
        _ ≤ 1 := hc0ξ
    · nlinarith
  have hvint : ∀ k' : ℕ, 1 ≤ k' → IntervalIntegrable (v k') volume 0 1 := by
    intro k' _
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      have : 1 ≤ Real.sqrt (max 1 ((k' : ℝ) * (1 - t))) := by
        rw [Real.one_le_sqrt]; exact le_max_left _ _
      linarith
  refine ⟨ρ + ρhat * (D * Real.pi), by positivity, ?_⟩
  intro k hk sel hsel
  have hmain := h53 k hk (midpointSchedule k) v hvprop hvint sel hsel
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- the integral bound
  set f : ℝ → ℝ := fun t => min 1 (ρ' * (midpointSchedule k).F k (v k t) t) with hf
  set h : ℝ → ℝ := fun t => 2 * D / (1 + ((k : ℝ) - (k : ℝ) * t) ^ 2) with hh
  have hhint : IntervalIntegrable h volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by fun_prop)
    intro t; positivity
  have hhval : ∫ t in (0 : ℝ)..1, h t = 2 * D * (k : ℝ)⁻¹ * Real.arctan k := by
    have e := intervalIntegral.integral_comp_sub_mul (a := (0 : ℝ)) (b := 1)
      (fun x : ℝ => 2 * D * (1 + x ^ 2)⁻¹) (ne_of_gt hk0) (k : ℝ)
    simp only [mul_one, mul_zero, sub_self, sub_zero] at e
    have hI0 : ∫ x in (0 : ℝ)..(k : ℝ), (1 + x ^ 2)⁻¹ = Real.arctan k := by
      simpa using (integral_inv_one_add_sq (a := (0 : ℝ)) (b := (k : ℝ)))
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hI0,
      smul_eq_mul] at e
    have : (fun t : ℝ => h t) = fun x => 2 * D * (1 + ((k : ℝ) - (k : ℝ) * x) ^ 2)⁻¹ := by
      funext t; simp only [hh, div_eq_mul_inv]
    rw [this, intervalIntegral.integral_const_mul, e]; ring
  have hfh : ∫ t in (0 : ℝ)..1, f t ≤ ∫ t in (0 : ℝ)..1, h t := by
    by_cases hfint : IntervalIntegrable f volume 0 1
    · apply intervalIntegral.integral_mono_on (by norm_num) hfint hhint
      intro t ht
      exact GoalAux.integrand_bound k hk c0 ρ' D hc0pos hρ' hD1 (le_max_right _ _) t ht.1 ht.2
    · rw [intervalIntegral.integral_undef hfint, hhval]
      have : 0 ≤ Real.arctan k := by
        rw [← Real.arctan_zero]; exact Real.arctan_mono hk0.le
      positivity
  have hkint : (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤ D * Real.pi := by
    calc (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤ (k : ℝ) * ∫ t in (0 : ℝ)..1, h t :=
          mul_le_mul_of_nonneg_left hfh hk0.le
      _ = 2 * D * Real.arctan k := by rw [hhval]; field_simp
      _ ≤ 2 * D * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left (Real.arctan_lt_pi_div_two _).le (by positivity)
      _ = D * Real.pi := by ring
  have : ρhat * (k : ℝ) * ∫ t in (0 : ℝ)..1, f t ≤ ρhat * (D * Real.pi) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hkint hρhat.le
  linarith
