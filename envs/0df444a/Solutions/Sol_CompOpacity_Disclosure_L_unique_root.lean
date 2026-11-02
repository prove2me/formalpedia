-- Prove2me | solution 1 for CompOpacity.Disclosure.L_unique_root
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T15:48:40.227747+00:00
-- url     : https://prove2.me/submissions/08ad2ad9-5165-44a0-86bf-f5e2a2fc19fe

import Mathlib
import Definitions.Def_CompOpacity_Disclosure_Model


namespace CompOpacity.Disclosure

theorem quartic_root (A0 A1 A2 A3 A4 : ℝ) (h0 : 0 < A0) (h1 : 0 ≤ A1) (h4 : A4 < 0)
    (h23 : A3 ≤ 0 ∨ 0 ≤ A2) :
    let Q : ℝ → ℝ := fun x => A0 + A1 * x + A2 * x ^ 2 + A3 * x ^ 3 + A4 * x ^ 4
    ∃ Δ : ℝ, 0 < Δ ∧ Q Δ = 0 ∧ ∀ x : ℝ, 0 < x → (Q x < 0 ↔ Δ < x) ∧ (Q x = 0 → x = Δ) := by
  intro Q
  -- h: Q x / x^k strictly decreasing on (0, ∞)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ∀ x y : ℝ, 0 < x → x < y → Q y / y ^ k < Q x / x ^ k := by
    rcases h23 with h3 | h2
    · refine ⟨2, fun x y hx hxy => ?_⟩
      have hy : 0 < y := hx.trans hxy
      have e : ∀ z : ℝ, 0 < z → Q z / z ^ 2 = A0 / z ^ 2 + A1 / z + A2 + A3 * z + A4 * z ^ 2 := by
        intro z hz; simp only [Q]; field_simp
      rw [e x hx, e y hy]
      have t0 : A0 / y ^ 2 < A0 / x ^ 2 := div_lt_div_of_pos_left h0 (by positivity) (by gcongr)
      have t1 : A1 / y ≤ A1 / x := div_le_div_of_nonneg_left h1 hx hxy.le
      have t3 : A3 * y ≤ A3 * x := mul_le_mul_of_nonpos_left hxy.le h3
      have t4 : A4 * y ^ 2 ≤ A4 * x ^ 2 := mul_le_mul_of_nonpos_left (by gcongr) h4.le
      linarith
    · refine ⟨3, fun x y hx hxy => ?_⟩
      have hy : 0 < y := hx.trans hxy
      have e : ∀ z : ℝ, 0 < z → Q z / z ^ 3 = A0 / z ^ 3 + A1 / z ^ 2 + A2 / z + A3 + A4 * z := by
        intro z hz; simp only [Q]; field_simp
      rw [e x hx, e y hy]
      have t0 : A0 / y ^ 3 < A0 / x ^ 3 := div_lt_div_of_pos_left h0 (by positivity) (by gcongr)
      have t1 : A1 / y ^ 2 ≤ A1 / x ^ 2 := div_le_div_of_nonneg_left h1 (by positivity) (by gcongr)
      have t2 : A2 / y ≤ A2 / x := div_le_div_of_nonneg_left h2 hx hxy.le
      have t4 : A4 * y ≤ A4 * x := mul_le_mul_of_nonpos_left hxy.le h4.le
      linarith
  have hQc : Continuous Q := by simp only [Q]; fun_prop
  -- a point where Q < 0
  set S := A0 + A1 + |A2| + |A3| with hS
  set X := 1 + S / (-A4) with hX
  have hS0 : 0 < S := by positivity
  have hX1 : 1 ≤ X := by rw [hX]; have : 0 ≤ S / (-A4) := div_nonneg hS0.le (by linarith); linarith
  have hQX : Q X < 0 := by
    have hX0 : 0 < X := by linarith
    have b2 : A2 * X ^ 2 ≤ |A2| * X ^ 3 := by
      calc A2 * X ^ 2 ≤ |A2| * X ^ 2 := by gcongr; exact le_abs_self _
        _ ≤ |A2| * X ^ 3 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 (by norm_num)) (abs_nonneg _)
    have b3 : A3 * X ^ 3 ≤ |A3| * X ^ 3 := by gcongr; exact le_abs_self _
    have b1 : A1 * X ≤ A1 * X ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ h1
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ 3 := pow_le_pow_right₀ hX1 (by norm_num)
    have b0 : A0 ≤ A0 * X ^ 3 := by
      have : 1 ≤ X ^ 3 := one_le_pow₀ hX1
      nlinarith
    have key : S * X ^ 3 + A4 * X ^ 4 < 0 := by
      have : S + A4 * X < 0 := by
        have hA : A4 ≠ 0 := h4.ne
        have e : A4 * (S / -A4) = -S := by rw [div_neg, mul_neg, mul_div_cancel₀ _ hA]
        rw [hX, mul_add, e]; linarith
      have hX3 : 0 < X ^ 3 := by positivity
      nlinarith
    simp only [Q]
    nlinarith
  have hQ0 : Q 0 = A0 := by simp [Q]
  obtain ⟨Δ, hΔ, hQΔ⟩ : ∃ Δ ∈ Set.Icc 0 X, Q Δ = 0 :=
    intermediate_value_Icc' (by linarith) hQc.continuousOn ⟨hQX.le, by rw [hQ0]; exact h0.le⟩
  have hΔ0 : 0 < Δ := by
    rcases eq_or_lt_of_le hΔ.1 with h | h
    · rw [← h, hQ0] at hQΔ; linarith
    · exact h
  refine ⟨Δ, hΔ0, hQΔ, fun x hx => ⟨?_, ?_⟩⟩
  · have hΔk : Q Δ / Δ ^ k = 0 := by rw [hQΔ, zero_div]
    constructor
    · intro hQx
      by_contra hc; push_neg at hc
      rcases eq_or_lt_of_le hc with h | h
      · rw [h] at hQx; linarith
      · have := hk x Δ hx h
        rw [hΔk] at this
        have : Q x / x ^ k < 0 := div_neg_of_neg_of_pos hQx (by positivity)
        linarith
    · intro h
      have := hk Δ x hΔ0 h
      rw [hΔk] at this
      have hxk : 0 < x ^ k := by positivity
      exact (div_neg_iff.1 this).elim (fun h => by linarith [h.2]) (fun h => h.1)
  · intro hQx
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hk x Δ hx h; rw [hQΔ, hQx] at this; simp at this
    · have := hk Δ x hΔ0 h; rw [hQΔ, hQx] at this; simp at this

theorem L_unique_root_proof (a : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) : ∃ Δ : ℝ, 0 < Δ ∧ Lpoly a Δ = 0 ∧ (∀ x : ℝ, 0 < x → Lpoly a x = 0 → x = Δ) ∧ ∀ x : ℝ, 0 < x → (Lpoly a x < 0 ↔ Δ < x) := by
  have hA4 : 0 < 6 - a * (30 - a * (52 - 31 * a)) := by
    nlinarith [mul_pos ha0 ha0, mul_pos (mul_pos ha0 ha0) ha0, sq_nonneg (a - 0.5),
      mul_pos ha0 (by linarith : (0:ℝ) < 0.5 - a)]
  have h23 : -a * (12 + a * (-82 + a * (206 + a * (-226 + 91 * a)))) ≤ 0 ∨
      0 ≤ -3 * a * (2 - 3 * a) * (1 - 5 * (1 - a) * a) := by
    by_cases h2 : 0 < 5 * a ^ 2 - 5 * a + 1
    · left
      have hp : 0 < 12 - 82 * a + 206 * a ^ 2 - 226 * a ^ 3 + 91 * a ^ 4 := by
        have : a < 0.28 := by nlinarith
        nlinarith [mul_pos ha0 ha0, mul_pos (mul_pos ha0 ha0) ha0, sq_nonneg (a - 0.28),
          mul_pos ha0 (by linarith : (0:ℝ) < 0.28 - a)]
      have : 12 + a * (-82 + a * (206 + a * (-226 + 91 * a))) =
          12 - 82 * a + 206 * a ^ 2 - 226 * a ^ 3 + 91 * a ^ 4 := by ring
      rw [this]; nlinarith
    · right
      push_neg at h2
      have : 1 - 5 * (1 - a) * a = 5 * a ^ 2 - 5 * a + 1 := by ring
      rw [this]
      have : 0 < 3 * a * (2 - 3 * a) := by nlinarith
      nlinarith
  obtain ⟨Δ, h1, h2, h3⟩ := quartic_root (a ^ 2) (3 * a ^ 2 * (2 - 3 * a))
    (-3 * a * (2 - 3 * a) * (1 - 5 * (1 - a) * a))
    (-a * (12 + a * (-82 + a * (206 + a * (-226 + 91 * a)))))
    (-(1 - a) * a * (1 - 2 * a) * (6 - a * (30 - a * (52 - 31 * a))))
    (by positivity) (by have : 0 < 2 - 3 * a := by linarith
                        positivity)
    (by have : 0 < (1 - a) * a * (1 - 2 * a) * (6 - a * (30 - a * (52 - 31 * a))) := by
          apply mul_pos (mul_pos (mul_pos (by linarith) ha0) (by linarith)) hA4
        linarith) h23
  exact ⟨Δ, h1, h2, fun x hx => (h3 x hx).2, fun x hx => (h3 x hx).1⟩

end CompOpacity.Disclosure

open CompOpacity.Disclosure in
theorem solution (a : ℝ) (ha0 : 0 < a) (ha : a < 1 / 2) : ∃ Δ : ℝ, 0 < Δ ∧ Lpoly a Δ = 0 ∧ (∀ x : ℝ, 0 < x → Lpoly a x = 0 → x = Δ) ∧ ∀ x : ℝ, 0 < x → (Lpoly a x < 0 ↔ Δ < x) :=
  L_unique_root_proof a ha0 ha
