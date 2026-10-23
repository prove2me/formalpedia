-- Prove2me | solution 1 for CrowdSignal.TwoPrice.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T15:52:42.427766+00:00
-- url     : https://prove2.me/submissions/b7e5cb76-4c86-4345-af1f-bf95b2402d7a

import Mathlib
import Definitions.Def_CrowdSignal_TwoPrice_Setting

open CrowdSignal.TwoPrice

namespace CS2Aux

lemma succ_of_lt {qj p : ℝ} (hq : 0 < qj) (hp : p < qj) :
    CrowdSignal.OnePrice.succ qj p = 1 - p / qj := by
  unfold CrowdSignal.OnePrice.succ
  have : p / qj < 1 := (div_lt_one hq).2 hp
  rw [max_eq_right (by linarith)]

lemma succ_of_ge {qj p : ℝ} (hq : 0 < qj) (hp : qj ≤ p) :
    CrowdSignal.OnePrice.succ qj p = 0 := by
  unfold CrowdSignal.OnePrice.succ
  have : 1 ≤ p / qj := (one_le_div hq).2 hp
  rw [max_eq_left (by linarith)]

lemma payoff_zero (P : Params) {qi qj p t : ℝ} (hq : 0 < qj) (hp : qj ≤ p) :
    payoff P qi qj (p, t) = 0 := by
  simp [payoff, succ_of_ge hq hp]

lemma payoff_A (P : Params) {qi qj p t : ℝ} (hq : 0 < qj) (hp : p < qj)
    (ht : p * qi / qj < t) :
    payoff P qi qj (p, t) = (1 - p/qj) * p +
      (P.α + (1 - P.α) * (1 - p/qj)) * (t * max 0 (1 - t/qi)) := by
  have hs : 0 < 1 - p / qj := by have := (div_lt_one hq).2 hp; linarith
  simp only [payoff, buyA, succ_of_lt hq hp, if_neg (not_le.2 ht)]
  have key : (1 - p/qj) * max 0 ((1 - t/qi) / (1 - p/qj)) = max 0 (1 - t/qi) := by
    rcases le_total (1 - t/qi) 0 with h | h
    · rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg h hs.le), max_eq_left h]; ring
    · rw [max_eq_right (div_nonneg h hs.le), max_eq_right h, mul_div_assoc']
      exact mul_div_cancel_left₀ _ hs.ne'
  linear_combination (P.α * t) * key

lemma payoff_B (P : Params) {qi qj p t : ℝ} (hq : 0 < qj) (hp : p < qj)
    (ht : t ≤ p * qi / qj) :
    payoff P qi qj (p, t) =
      (1 - p/qj) * (p + P.α * t + (1 - P.α) * (t * max 0 (1 - t/qi))) := by
  simp only [payoff, buyA, succ_of_lt hq hp, if_pos ht]; ring

lemma payoff_le (P : Params) (ha0 : 0 ≤ P.α) {qi qj p t : ℝ} (hqi : 0 < qi) (hq : 0 < qj)
    (hp : p < qj) (ht0 : 0 ≤ t) :
    payoff P qi qj (p, t) ≤ (1 - p/qj) * p +
      (P.α + (1 - P.α) * (1 - p/qj)) * (t * max 0 (1 - t/qi)) := by
  by_cases ht : p * qi / qj < t
  · rw [payoff_A P hq hp ht]
  · push_neg at ht
    rw [payoff_B P hq hp ht]
    have h1 : 1 - p/qj ≤ 1 - t/qi := by
      have : t / qi ≤ p / qj := by
        rw [div_le_iff₀ hqi]
        calc t ≤ p*qi/qj := ht
          _ = p / qj * qi := by ring
      linarith
    have h2 : 1 - p/qj ≤ max 0 (1 - t/qi) := le_trans h1 (le_max_right _ _)
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg ha0 ht0)]

lemma g_le {q t : ℝ} (hq : 0 < q) : t * max 0 (1 - t/q) ≤ q/4 := by
  rcases le_total (1 - t/q) 0 with h | h
  · rw [max_eq_left h]; linarith
  · rw [max_eq_right h]
    have : t * (1 - t/q) = q/4 - (t - q/2)^2/q := by field_simp; ring
    rw [this]; have := div_nonneg (sq_nonneg (t - q/2)) hq.le; linarith

lemma g_eq_quarter {q t : ℝ} (hq : 0 < q) (h : q/4 ≤ t * max 0 (1 - t/q)) : t = q/2 := by
  rcases le_total (1 - t/q) 0 with h' | h'
  · rw [max_eq_left h'] at h; linarith
  · rw [max_eq_right h'] at h
    have : t * (1 - t/q) = q/4 - (t - q/2)^2/q := by field_simp; ring
    rw [this] at h
    have h3 : (t - q/2)^2/q ≤ 0 := by linarith
    have h4 : (t - q/2)^2 ≤ 0 := by
      have := (div_le_iff₀ hq).1 h3; linarith
    nlinarith [sq_nonneg (t - q/2)]

lemma g_ge {q t : ℝ} (ht : 0 ≤ t) : t * (1 - t/q) ≤ t * max 0 (1 - t/q) :=
  mul_le_mul_of_nonneg_left (le_max_right _ _) ht

lemma g_eq {q t : ℝ} (hq : 0 < q) (h : t ≤ q) : t * max 0 (1 - t/q) = t * (1 - t/q) := by
  rw [max_eq_right]; have := (div_le_one hq).2 h; linarith

lemma g_zero {q t : ℝ} (hq : 0 < q) (h : q ≤ t) : t * max 0 (1 - t/q) = 0 := by
  rw [max_eq_left]; · ring
  have := (one_le_div hq).2 h; linarith

/-- the full-information optimum for a type believed to be its own quality. -/
lemma qq_bound (P : Params) (ha0 : 0 < P.α) (ha1 : P.α < 1) {q p t : ℝ} (hq : 0 < q)
    (hp0 : 0 ≤ p) (ht : 0 < t) :
    payoff P q q (p, t) ≤ (P.α^2 + 6*P.α + 25) * q / 64 ∧
    ((P.α^2 + 6*P.α + 25) * q / 64 ≤ payoff P q q (p, t) →
      p = (3 + P.α) / 8 * q ∧ t = q / 2) := by
  have hK : 0 < (P.α^2 + 6*P.α + 25) * q / 64 := by positivity
  by_cases hp : p < q
  · have hle := payoff_le P ha0.le hq hq hp ht.le
    have hg := g_le (t := t) hq
    set g := t * max 0 (1 - t/q) with hgdef
    set u := p / q with hu
    have hpu : p = u * q := by rw [hu]; field_simp
    have hu0 : 0 ≤ u := div_nonneg hp0 hq.le
    have hu1 : u < 1 := (div_lt_one hq).2 hp
    have hc : 0 < P.α + (1 - P.α) * (1 - u) := by nlinarith
    have key : (1 - u) * p + (P.α + (1 - P.α) * (1 - u)) * g =
        (P.α^2 + 6*P.α + 25) * q / 64 - q * (u - (3 + P.α)/8)^2
          - (P.α + (1 - P.α) * (1 - u)) * (q/4 - g) := by
      rw [hpu]; ring
    have h1 : 0 ≤ q * (u - (3 + P.α)/8)^2 := by positivity
    have h2 : 0 ≤ (P.α + (1 - P.α) * (1 - u)) * (q/4 - g) :=
      mul_nonneg hc.le (by linarith)
    refine ⟨by linarith, fun hge => ?_⟩
    have e1 : q * (u - (3 + P.α)/8)^2 = 0 := by linarith
    have e2 : (P.α + (1 - P.α) * (1 - u)) * (q/4 - g) = 0 := by linarith
    have e1' : u = (3 + P.α)/8 := by
      rcases mul_eq_zero.1 e1 with h | h
      · linarith
      · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h; linarith
    have e2' : g = q/4 := by
      rcases mul_eq_zero.1 e2 with h | h
      · linarith
      · linarith
    refine ⟨by rw [hpu, e1'], g_eq_quarter hq (by rw [← hgdef, e2'])⟩
  · push_neg at hp
    rw [payoff_zero P hq hp]
    exact ⟨hK.le, fun h => absurd h (not_le.2 hK)⟩

lemma qq_value (P : Params) (ha0 : 0 < P.α) (ha1 : P.α < 1) {q : ℝ} (hq : 0 < q) :
    payoff P q q ((3 + P.α) / 8 * q, q / 2) = (P.α^2 + 6*P.α + 25) * q / 64 := by
  rw [payoff_A P hq (by nlinarith) (by
    have : (3 + P.α) / 8 * q * q / q = (3 + P.α) / 8 * q := by field_simp
    rw [this]; nlinarith), g_eq hq (by linarith)]
  field_simp; ring

end CS2Aux

namespace CS2Aux

lemma W_eq (P : Params) {qi qj p t : ℝ} (hq : 0 < qj) (hp : p < qj) :
    W P qi qj p t = (1 - p/qj) * p + (P.α + (1 - P.α) * (1 - p/qj)) * (t - t^2/qi) := by
  have hs : 1 - p / qj ≠ 0 := by have := (div_lt_one hq).2 hp; linarith
  unfold W
  have e : (1 - p/qj) * (P.α / (1 - p/qj)) = P.α := by
    rw [mul_div_assoc']; exact mul_div_cancel_left₀ _ hs
  linear_combination ((1 - t/qi) * t) * e

lemma optL (P : Params) (hP : P.Standing) (hTL : P.T ≤ (3 + P.α) / 8 * P.qL) :
    IsGreatest (payoff P P.qL P.qL '' {x | Feas P x})
      ((P.α^2 + 6*P.α + 25) * P.qL / 64) ∧
    optPayoff P P.qL P.qL = (P.α^2 + 6*P.α + 25) * P.qL / 64 := by
  obtain ⟨hL, hLH, ha0, ha1, hT⟩ := hP
  have hG : IsGreatest (payoff P P.qL P.qL '' {x | Feas P x})
      ((P.α^2 + 6*P.α + 25) * P.qL / 64) := by
    refine ⟨⟨((3 + P.α) / 8 * P.qL, P.qL / 2), ⟨hTL, by linarith⟩, qq_value P ha0 ha1 hL⟩, ?_⟩
    rintro v ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩
    exact (qq_bound P ha0 ha1 hL (by simp at hp; linarith) ht).1
  exact ⟨hG, hG.csSup_eq⟩

end CS2Aux

namespace CS2Aux

lemma lagr (a H L p t p0 t0 : ℝ) (hH : H ≠ 0) (hL : L ≠ 0)
    (hline : 4 * p0 + (1 - a) * t0 = 2 * H) :
    H * (2 * t0 - L) *
      (((1 - p/H) * p + (a + (1 - a) * (1 - p/H)) * (t - t^2/H)) -
       ((1 - p0/H) * p0 + (a + (1 - a) * (1 - p0/H)) * (t0 - t0^2/H))) =
    L * (2 * t0 - H) *
      (((1 - p/H) * p + (a + (1 - a) * (1 - p/H)) * (t - t^2/L)) -
       ((1 - p0/H) * p0 + (a + (1 - a) * (1 - p0/H)) * (t0 - t0^2/L)))
    - 2 * t0 * (H - L) * (p - p0)^2 / H
    - (a + (1 - a) * (1 - p/H)) * (H - L) * (t - t0)^2 := by
  have hp0 : p0 = (2 * H - (1 - a) * t0) / 4 := by linarith
  subst hp0
  field_simp
  ring

/-- Facts about the dotted pair. -/
lemma dot_facts (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (p0 t0 : ℝ) (h2 : P.qH / 2 < t0) (hline : 4 * p0 + (1 - P.α) * t0 = 2 * P.qH)
    (hG : (1 - p0/P.qH) * p0 + (P.α + (1 - P.α) * (1 - p0/P.qH)) * (t0 - t0^2/P.qL) =
      (P.α^2 + 6*P.α + 25) * P.qL / 64) :
    p0 < (3 + P.α) / 8 * P.qH ∧ p0 < t0 ∧ t0 < P.qL ∧
    0 < P.α + (1 - P.α) * (1 - p0/P.qH) ∧
    P.qH / 4 ≤ (P.α^2 + 6*P.α + 25) * P.qL / 64 ∧
    (1 - p0/P.qH) * p0 + (P.α + (1 - P.α) * (1 - p0/P.qH)) * (t0 - t0^2/P.qH) =
      (P.α^2 + 6*P.α + 25) * P.qL / 64 +
        (P.α + (1 - P.α) * (1 - p0/P.qH)) * t0^2 * (1/P.qL - 1/P.qH) ∧
    (P.α^2 + 2*P.α + 5) * P.qH * (P.qH - P.qL) / (32 * P.qL) <
        (P.α + (1 - P.α) * (1 - p0/P.qH)) * t0^2 * (1/P.qL - 1/P.qH) := by
  obtain ⟨hL, hLH, ha0, ha1, hT⟩ := hP
  set a := P.α with ha
  set L := P.qL with hLdef
  set H := P.qH with hHdef
  have hH : 0 < H := by linarith
  have hp0lt : p0 < (3 + a) / 8 * H := by nlinarith
  have hp0t0 : p0 < t0 := by nlinarith
  have hu : p0 / H < (3 + a) / 8 := by rw [div_lt_iff₀ hH]; linarith
  have hc0 : (a^2 + 2*a + 5)/8 < a + (1 - a) * (1 - p0/H) := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - a) (by linarith : (0:ℝ) < (3 + a)/8 - p0/H)]
  have hc0pos : 0 < a + (1 - a) * (1 - p0/H) := by nlinarith
  have hK : H / 4 ≤ (a^2 + 6*a + 25) * L / 64 := by linarith
  -- t0 < L
  have ht0L : t0 < L := by
    by_contra hcon
    push_neg at hcon
    have h1 : t0 - t0^2/L ≤ 0 := by
      have : t0 - t0^2/L = t0 * (1 - t0/L) := by ring
      rw [this]
      have : 1 ≤ t0 / L := (one_le_div hL).2 hcon
      nlinarith
    have h3 : (1 - p0/H) * p0 = H/4 - (p0 - H/2)^2/H := by field_simp; ring
    have h4 : 0 ≤ (p0 - H/2)^2/H := by positivity
    have h5 : (a + (1 - a) * (1 - p0/H)) * (t0 - t0^2/L) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc0pos.le h1
    have h6 : (p0 - H/2)^2/H = 0 := by linarith
    have h7 : (p0 - H/2)^2 = 0 := by
      rcases div_eq_zero_iff.1 h6 with h | h
      · exact h
      · linarith
    have h8 : p0 = H/2 := by nlinarith [sq_nonneg (p0 - H/2)]
    have : (1 - a) * t0 = 0 := by linarith
    have : 0 < (1 - a) * t0 := mul_pos (by linarith) (by linarith)
    linarith
  have hO : (1 - p0/H) * p0 + (a + (1 - a) * (1 - p0/H)) * (t0 - t0^2/H) =
      (a^2 + 6*a + 25) * L / 64 + (a + (1 - a) * (1 - p0/H)) * t0^2 * (1/L - 1/H) := by
    rw [← hG]; ring
  have hsq : H^2/4 < t0^2 := by nlinarith
  have hprod : (a^2 + 2*a + 5)/8 * (H^2/4) < (a + (1 - a) * (1 - p0/H)) * t0^2 :=
    mul_lt_mul'' hc0 hsq (by positivity) (by positivity)
  have hδ : 1/L - 1/H = (H - L) / (L * H) := by field_simp
  have hδpos : 0 < (H - L) / (L * H) := div_pos (by linarith) (by positivity)
  have hE : (a^2 + 2*a + 5) * H * (H - L) / (32 * L) =
      (a^2 + 2*a + 5)/8 * (H^2/4) * ((H - L) / (L * H)) := by field_simp; ring
  refine ⟨hp0lt, hp0t0, ht0L, hc0pos, hK, hO, ?_⟩
  rw [hE, hδ]
  exact mul_lt_mul_of_pos_right hprod hδpos

end CS2Aux

namespace CS2Aux

lemma HL_bound (P : Params) (hP : P.Standing) {p t : ℝ} (hp : 0 ≤ p) (ht : 0 < t) :
    payoff P P.qH P.qL (p, t) ≤ (P.α^2 + 6*P.α + 25) * P.qL / 64 +
      (P.α^2 + 2*P.α + 5) * P.qH * (P.qH - P.qL) / (32 * P.qL) := by
  obtain ⟨hL, hLH, ha0, ha1, hT⟩ := hP
  set a := P.α with ha
  set L := P.qL with hLdef
  set H := P.qH with hHdef
  have hH : 0 < H := by linarith
  have hEpos : 0 ≤ (a^2 + 2*a + 5) * H * (H - L) / (32 * L) := by
    apply div_nonneg _ (by positivity)
    apply mul_nonneg (by positivity) (by linarith)
  by_cases hpL : p < L
  · have hle := payoff_le P ha0.le hH hL hpL ht.le
    have hg := g_le (t := t) hH
    have hu1 : p / L < 1 := (div_lt_one hL).2 hpL
    have hu0 : 0 ≤ p / L := div_nonneg hp hL.le
    have hc : 0 ≤ a + (1 - a) * (1 - p/L) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hg hc
    have hid : (a^2 + 6*a + 25) * L / 64 + (a^2 + 2*a + 5) * H * (H - L) / (32 * L) -
        ((1 - p/L) * p + (a + (1 - a) * (1 - p/L)) * (H/4)) =
        ((a + 3)^2 * (H - L)^2 + (8 * p - 4 * L + (1 - a) * H)^2) / (64 * L) := by
      field_simp; ring
    have h2 : 0 ≤ ((a + 3)^2 * (H - L)^2 + (8 * p - 4 * L + (1 - a) * H)^2) / (64 * L) := by
      positivity
    linarith
  · push_neg at hpL
    rw [payoff_zero P hL hpL]; positivity

lemma LH_ge_LL (P : Params) (hP : P.Standing) {p t : ℝ} (hp : 0 ≤ p) (hpt : p < t) :
    payoff P P.qL P.qL (p, t) ≤ payoff P P.qL P.qH (p, t) := by
  obtain ⟨hL, hLH, ha0, ha1, hT⟩ := hP
  have hH : 0 < P.qH := by linarith
  by_cases hpL : p < P.qL
  · have hpH : p < P.qH := by linarith
    rw [payoff_A P hL hpL (by rw [mul_div_assoc, div_self hL.ne']; linarith),
      payoff_A P hH hpH (by
        have : p * P.qL / P.qH ≤ p := by
          rw [div_le_iff₀ hH]; nlinarith
        linarith)]
    have hg : 0 ≤ t * max 0 (1 - t / P.qL) :=
      mul_nonneg (by linarith) (le_max_left _ _)
    have hdiv : p / P.qH ≤ p / P.qL := div_le_div_of_nonneg_left hp hL hLH.le
    have : 0 ≤ (p / P.qL - p / P.qH) * (p + (1 - P.α) * (t * max 0 (1 - t / P.qL))) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  · push_neg at hpL
    rw [payoff_zero P hL hpL]
    have hpH : p < P.qH ∨ P.qH ≤ p := lt_or_ge p P.qH
    rcases hpH with hpH | hpH
    · have hle : 0 ≤ payoff P P.qL P.qH (p, t) := by
        unfold payoff CrowdSignal.OnePrice.succ buyA
        apply mul_nonneg (le_max_left _ _)
        have h1 : 0 ≤ P.α * t * (if t ≤ p * P.qL / P.qH then 1
            else max 0 ((1 - t / P.qL) / (1 - p / P.qH))) := by
          apply mul_nonneg (mul_nonneg ha0.le (by linarith))
          split_ifs
          · norm_num
          · exact le_max_left _ _
        have h2 : 0 ≤ (1 - P.α) * t * max 0 (1 - t / P.qL) :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) (le_max_left _ _)
        linarith
      exact hle
    · rw [payoff_zero P hH hpH]

end CS2Aux


open CrowdSignal.TwoPrice

namespace CS2Aux

lemma psi_mono (a u w : ℝ) (ha1 : a < 1) (hwu : w ≤ u) (hum : 2 * (1 - a) * u ≤ 1) :
    a * w + (1 - a) * w * (1 - w) ≤ a * u + (1 - a) * u * (1 - u) := by
  have h1 : (1 - a) * (u + w) ≤ 1 := by nlinarith
  have := mul_nonneg (sub_nonneg.2 hwu) (sub_nonneg.2 h1)
  nlinarith

lemma psi_le (a w m : ℝ) (ha1 : a < 1) (hm : 2 * (1 - a) * m = 1) :
    a * w + (1 - a) * w * (1 - w) ≤ a * m + (1 - a) * m * (1 - m) := by
  have e : (a * m + (1 - a) * m * (1 - m)) - (a * w + (1 - a) * w * (1 - w)) =
      (1 - a) * (m - w)^2 + (m - w) * (1 - 2 * (1 - a) * m) := by ring
  rw [hm, sub_self, mul_zero, add_zero] at e
  have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) (sq_nonneg (m - w))
  linarith

lemma h_dec (a qi qj t u : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hqi : 0 < qi) (hqj : 0 < qj)
    (ht : 1/2 ≤ t) (htu : t ≤ u) (hu : u ≤ 1) :
    (1 - u) * (qj * u + qi * (a * u + (1 - a) * u * (1 - u))) ≤
      (1 - t) * (qj * t + qi * (a * t + (1 - a) * t * (1 - t))) := by
  have hR : 0 ≤ (a - 1) * (t^2 + t*u + u^2) + (2 - a) * (t + u) - 1 := by
    have P1 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) (by linarith : (0:ℝ) ≤ t - 1/2))
      (by linarith : (0:ℝ) ≤ 1 - t)
    have P2 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) (by linarith : (0:ℝ) ≤ u - 1/2))
      (by linarith : (0:ℝ) ≤ 1 - u)
    have P3 := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) (by linarith : (0:ℝ) ≤ t - 1/2))
      (by linarith : (0:ℝ) ≤ 1 - u)
    have P4 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - t) (by linarith : (0:ℝ) ≤ 1 - a)
    have P5 := mul_nonneg ha0.le (by linarith : (0:ℝ) ≤ t - 1/2)
    have P6 := mul_nonneg ha0.le (by linarith : (0:ℝ) ≤ u - 1/2)
    nlinarith
  have hQ : 0 ≤ qj * (t + u - 1) + qi * ((a - 1) * (t^2 + t*u + u^2) + (2 - a) * (t + u) - 1) :=
    add_nonneg (mul_nonneg hqj.le (by linarith)) (mul_nonneg hqi.le hR)
  have e : (1 - t) * (qj * t + qi * (a * t + (1 - a) * t * (1 - t))) -
      (1 - u) * (qj * u + qi * (a * u + (1 - a) * u * (1 - u))) =
      (u - t) * (qj * (t + u - 1) + qi * ((a - 1) * (t^2 + t*u + u^2) + (2 - a) * (t + u) - 1)) := by
    ring
  have := mul_nonneg (sub_nonneg.2 htu) hQ
  linarith

lemma k_dec (qi qj M t u : ℝ) (hqi : 0 < qi) (hqj : 0 < qj) (hM : 0 ≤ M)
    (ht : 1/2 ≤ t) (htu : t ≤ u) :
    (1 - u) * (qj * u + qi * M) ≤ (1 - t) * (qj * t + qi * M) := by
  have e : (1 - t) * (qj * t + qi * M) - (1 - u) * (qj * u + qi * M) =
      (u - t) * (qj * (u + t - 1) + qi * M) := by ring
  have h1 : 0 ≤ qj * (u + t - 1) := mul_nonneg hqj.le (by linarith)
  have h2 : 0 ≤ qi * M := mul_nonneg hqi.le hM
  have := mul_nonneg (sub_nonneg.2 htu) (add_nonneg h1 h2)
  linarith

lemma reg2_arith (a qi qj τ u w : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hqi : 0 < qi) (hqj : 0 < qj)
    (hτ : 1/2 ≤ τ) (hτu : τ ≤ u) (hu : u < 1) (hτm : 2 * (1 - a) * τ < 1) (hwu : w ≤ u) :
    (1 - u) * (qj * u + qi * (a * w + (1 - a) * w * (1 - w))) ≤
      (1 - τ) * (qj * τ + qi * (a * τ + (1 - a) * τ * (1 - τ))) := by
  have h1u : 0 ≤ 1 - u := by linarith
  by_cases hum : 2 * (1 - a) * u ≤ 1
  · have h1 := psi_mono a u w ha1 hwu hum
    have h2 : (1 - u) * (qj * u + qi * (a * w + (1 - a) * w * (1 - w))) ≤
        (1 - u) * (qj * u + qi * (a * u + (1 - a) * u * (1 - u))) :=
      mul_le_mul_of_nonneg_left (by nlinarith) h1u
    have h3 := h_dec a qi qj τ u ha0 ha1 hqi hqj hτ hτu hu.le
    linarith
  · push_neg at hum
    set m := 1 / (2 * (1 - a)) with hmdef
    have hm : 2 * (1 - a) * m = 1 := by
      have : (1 - a) ≠ 0 := (by linarith : (0:ℝ) < 1 - a).ne'
      rw [hmdef]; field_simp
    have hτm' : τ ≤ m := by nlinarith
    have hmu : m ≤ u := by nlinarith
    have h1 := psi_le a w m ha1 hm
    have hM : 0 ≤ a * m + (1 - a) * m * (1 - m) := by
      have : a * m + (1 - a) * m * (1 - m) = m / 2 := by
        have : (1 - a) * m * (1 - m) = (1 - m) / 2 := by linear_combination (1 - m) / 2 * hm
        rw [this]; linear_combination (-1/2 : ℝ) * hm
      rw [this]; nlinarith
    have h2 : (1 - u) * (qj * u + qi * (a * w + (1 - a) * w * (1 - w))) ≤
        (1 - u) * (qj * u + qi * (a * m + (1 - a) * m * (1 - m))) :=
      mul_le_mul_of_nonneg_left (by nlinarith) h1u
    have h3 := k_dec qi qj _ m u hqi hqj hM (by linarith) hmu
    have h4 := h_dec a qi qj τ m ha0 ha1 hqi hqj hτ hτm' (by linarith)
    linarith

/-- High financing target: bound by the boundary price pair. -/
lemma hiT (P : Params) (ha0 : 0 < P.α) (ha1 : P.α < 1) {qi qj p t : ℝ} (hqi : 0 < qi)
    (hqj : 0 < qj) (hp : p < qj) (hp2 : qj / 2 ≤ p) (ht : 0 < t) :
    ∃ w, w ≤ p / qj ∧ payoff P qi qj (p, t) ≤
      (1 - p/qj) * (qj * (p/qj) + qi * (P.α * w + (1 - P.α) * w * (1 - w))) := by
  have hpq : qj * (p/qj) = p := by field_simp
  have hu1 : p / qj < 1 := (div_lt_one hqj).2 hp
  have hu2 : 1/2 ≤ p / qj := by rw [le_div_iff₀ hqj]; linarith
  by_cases hB : t ≤ p * qi / qj
  · refine ⟨t / qi, ?_, ?_⟩
    · rw [div_le_div_iff₀ hqi hqj]; rw [le_div_iff₀ hqj] at hB; linarith
    · rw [payoff_B P hqj hp hB, hpq]
      have hv : t / qi ≤ p / qj := by
        rw [div_le_div_iff₀ hqi hqj]; rw [le_div_iff₀ hqj] at hB; linarith
      rw [max_eq_right (by linarith)]
      apply le_of_eq
      field_simp
      ring
  · push_neg at hB
    refine ⟨p / qj, le_refl _, ?_⟩
    rw [payoff_A P hqj hp hB, hpq]
    have hv : p / qj < t / qi := by
      rw [div_lt_div_iff₀ hqj hqi]; rw [div_lt_iff₀ hqj] at hB; linarith
    have hg : t * max 0 (1 - t / qi) ≤ qi * ((p / qj) * (1 - p / qj)) := by
      rcases le_total (1 - t/qi) 0 with h | h
      · rw [max_eq_left h, mul_zero]
        exact mul_nonneg hqi.le (mul_nonneg (by linarith) (by linarith))
      · rw [max_eq_right h]
        have e : t * (1 - t/qi) = qi * ((t/qi) * (1 - t/qi)) := by field_simp
        rw [e]
        apply mul_le_mul_of_nonneg_left _ hqi.le
        nlinarith
    have hc : 0 ≤ P.α + (1 - P.α) * (1 - p / qj) := by nlinarith
    have := mul_le_mul_of_nonneg_left hg hc
    nlinarith

end CS2Aux


open CrowdSignal.TwoPrice

namespace CS2Aux

lemma reg1 (P : Params) (ha0 : 0 < P.α) (ha1 : P.α < 1) {qi qj T : ℝ} (hqi : 0 < qi)
    (hqj : 0 < qj) (hT0 : 0 < T) (hT : T ≤ qj / 2) (p t : ℝ) (hp : T ≤ p) (ht : 0 < t) :
    payoff P qi qj (p, t) ≤ payoff P qi qj (max ((4 * qj - (1 - P.α) * qi) / 8) T, qi / 2) := by
  set x := (4 * qj - (1 - P.α) * qi) / 8 with hx
  set P1 := max x T with hP1
  have hP1T : T ≤ P1 := le_max_right _ _
  have hxle : x ≤ qj / 2 := by
    rw [hx]; have : 0 ≤ (1 - P.α) * qi := mul_nonneg (by linarith) hqi.le
    linarith
  have hP1h : P1 ≤ qj / 2 := max_le hxle hT
  have hP1q : P1 < qj := by linarith
  have hu : P1 / qj ≤ 1/2 := by rw [div_le_iff₀ hqj]; linarith
  set V := (1 - P1/qj) * P1 + (P.α + (1 - P.α) * (1 - P1/qj)) * (qi / 4) with hV
  have hval : payoff P qi qj (P1, qi / 2) = V := by
    have e : qi / 2 / qi = 1 / 2 := by field_simp
    by_cases hA : P1 * qi / qj < qi / 2
    · rw [payoff_A P hqj hP1q hA, e, max_eq_right (by norm_num)]
      rw [hV]; ring
    · push_neg at hA
      have hP1e : P1 = qj / 2 := by
        have : qj / 2 ≤ P1 := by
          rw [le_div_iff₀ hqj] at hA
          nlinarith
        linarith
      rw [payoff_B P hqj hP1q hA, e, max_eq_right (by norm_num), hV, hP1e]
      field_simp; ring
  rw [hval]
  have hVpos : 0 ≤ V := by
    rw [hV]
    have h1 : 0 ≤ (1 - P1/qj) * P1 := mul_nonneg (by linarith) (by linarith)
    have h2 : 0 ≤ (P.α + (1 - P.α) * (1 - P1/qj)) * (qi / 4) :=
      mul_nonneg (by nlinarith) (by linarith)
    linarith
  by_cases hpq : p < qj
  · have hle := payoff_le P ha0.le hqi hqj hpq ht.le
    have hg := g_le (t := t) hqi
    have hu0 : 0 ≤ p / qj := div_nonneg (by linarith) hqj.le
    have hu1 : p / qj < 1 := (div_lt_one hqj).2 hpq
    have hc : 0 ≤ P.α + (1 - P.α) * (1 - p/qj) := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hg hc
    have hid : V - ((1 - p/qj) * p + (P.α + (1 - P.α) * (1 - p/qj)) * (qi / 4)) =
        ((p - x)^2 - (P1 - x)^2) / qj := by
      rw [hV, hx]; field_simp; ring
    have hsq : (P1 - x)^2 ≤ (p - x)^2 := by
      rcases max_choice x T with h | h
      · have he : P1 = x := hP1.trans h
        rw [he, sub_self]; norm_num; positivity
      · have he : P1 = T := hP1.trans h
        have hxT : x ≤ T := by rw [← he]; exact le_max_left _ _
        rw [he]
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    have : 0 ≤ ((p - x)^2 - (P1 - x)^2) / qj := div_nonneg (by linarith) hqj.le
    linarith
  · push_neg at hpq
    rw [payoff_zero P hqj hpq]; exact hVpos

lemma reg2 (P : Params) (ha0 : 0 < P.α) (ha1 : P.α < 1) {qi qj T : ℝ} (hqi : 0 < qi)
    (hqj : 0 < qj) (hT1 : qj / 2 < T) (hT2 : T < qj / (2 * (1 - P.α))) (hTj : T ≤ qj)
    (p t : ℝ) (hp : T ≤ p) (ht : 0 < t) :
    payoff P qi qj (p, t) ≤ payoff P qi qj (T, T * qi / qj) := by
  by_cases hTq : T < qj
  swap
  · have hTe : qj ≤ T := by linarith
    rw [payoff_zero P hqj hTe, payoff_zero P hqj (by linarith)]
  have hval : payoff P qi qj (T, T * qi / qj) = (1 - T/qj) * (qj * (T/qj) +
      qi * (P.α * (T/qj) + (1 - P.α) * (T/qj) * (1 - T/qj))) := by
    rw [payoff_B P hqj hTq (le_refl _)]
    have e : T * qi / qj / qi = T / qj := by field_simp
    have hτ1 : T / qj < 1 := (div_lt_one hqj).2 hTq
    rw [e, max_eq_right (by linarith)]
    field_simp; ring
  rw [hval]
  have hτ : 1/2 ≤ T / qj := by rw [le_div_iff₀ hqj]; linarith
  have hτ1 : T / qj < 1 := (div_lt_one hqj).2 hTq
  have hVpos : 0 ≤ (1 - T/qj) * (qj * (T/qj) +
      qi * (P.α * (T/qj) + (1 - P.α) * (T/qj) * (1 - T/qj))) := by
    apply mul_nonneg (by linarith)
    apply add_nonneg (mul_nonneg hqj.le (by linarith))
    apply mul_nonneg hqi.le
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P.α) (by linarith : (0:ℝ) ≤ T/qj))
      (by linarith : (0:ℝ) ≤ 1 - T/qj)
    nlinarith
  by_cases hpq : p < qj
  · obtain ⟨w, hw, hb⟩ := hiT P ha0 ha1 hqi hqj hpq (by linarith) ht
    have hτm : 2 * (1 - P.α) * (T / qj) < 1 := by
      have h1a : 0 < 2 * (1 - P.α) := by linarith
      rw [lt_div_iff₀ h1a] at hT2
      rw [show 2 * (1 - P.α) * (T / qj) = (T * (2 * (1 - P.α))) / qj by ring,
        div_lt_one hqj]
      exact hT2
    have hτu : T / qj ≤ p / qj := div_le_div_of_nonneg_right hp hqj.le
    have := reg2_arith P.α qi qj (T/qj) (p/qj) w ha0 ha1 hqi hqj hτ hτu
      ((div_lt_one hqj).2 hpq) hτm hw
    linarith
  · push_neg at hpq
    rw [payoff_zero P hqj hpq]; exact hVpos

lemma reg3 (P : Params) (ha0 : 0 < P.α) (ha1 : P.α < 1) {qi qj T : ℝ} (hqi : 0 < qi)
    (hqj : 0 < qj) (hT1 : qj ≤ 2 * (1 - P.α) * T) (hTj : T ≤ qj)
    (p t : ℝ) (hp : T ≤ p) (ht : 0 < t) :
    payoff P qi qj (p, t) ≤ payoff P qi qj (T, qi / (2 * (1 - P.α))) := by
  have h1a : 0 < 1 - P.α := by linarith
  have hT0 : qj / 2 < T := by nlinarith
  by_cases hTq : T < qj
  swap
  · have hTe : qj ≤ T := by linarith
    rw [payoff_zero P hqj hTe, payoff_zero P hqj (by linarith)]
  set m := 1 / (2 * (1 - P.α)) with hmdef
  have hm : 2 * (1 - P.α) * m = 1 := by rw [hmdef]; field_simp
  have hτ1 : T / qj < 1 := (div_lt_one hqj).2 hTq
  have hmτ : m ≤ T / qj := by
    rw [hmdef, div_le_div_iff₀ (by linarith) hqj]; linarith
  have hP2 : qi / (2 * (1 - P.α)) = m * qi := by rw [hmdef]; field_simp
  have hB : qi / (2 * (1 - P.α)) ≤ T * qi / qj := by
    rw [hP2, show T * qi / qj = T / qj * qi by ring]
    exact mul_le_mul_of_nonneg_right hmτ hqi.le
  have hval : payoff P qi qj (T, qi / (2 * (1 - P.α))) = (1 - T/qj) * (qj * (T/qj) +
      qi * (P.α * m + (1 - P.α) * m * (1 - m))) := by
    rw [payoff_B P hqj hTq hB, hP2]
    have e : m * qi / qi = m := by field_simp
    rw [e, max_eq_right (by linarith)]
    field_simp; ring
  rw [hval]
  have hM : 0 ≤ P.α * m + (1 - P.α) * m * (1 - m) := by
    have hm0 : 0 ≤ m := by rw [hmdef]; positivity
    have := mul_nonneg (mul_nonneg h1a.le hm0) (by linarith : (0:ℝ) ≤ 1 - m)
    nlinarith
  have hτ : 1/2 ≤ T / qj := by rw [le_div_iff₀ hqj]; linarith
  have hVpos : 0 ≤ (1 - T/qj) * (qj * (T/qj) + qi * (P.α * m + (1 - P.α) * m * (1 - m))) := by
    apply mul_nonneg (by linarith)
    exact add_nonneg (mul_nonneg hqj.le (by linarith)) (mul_nonneg hqi.le hM)
  by_cases hpq : p < qj
  · obtain ⟨w, hw, hb⟩ := hiT P ha0 ha1 hqi hqj hpq (by linarith) ht
    have hψ := psi_le P.α w m ha1 hm
    have hτu : T / qj ≤ p / qj := div_le_div_of_nonneg_right hp hqj.le
    have h1u : 0 ≤ 1 - p / qj := by have := (div_lt_one hqj).2 hpq; linarith
    have h2 : (1 - p/qj) * (qj * (p/qj) + qi * (P.α * w + (1 - P.α) * w * (1 - w))) ≤
        (1 - p/qj) * (qj * (p/qj) + qi * (P.α * m + (1 - P.α) * m * (1 - m))) :=
      mul_le_mul_of_nonneg_left (by nlinarith) h1u
    have h3 := k_dec qi qj _ (T/qj) (p/qj) hqi hqj hM hτ hτu
    linarith
  · push_neg at hpq
    rw [payoff_zero P hqj hpq]; exact hVpos

lemma greatest_of (P : Params) {qi qj : ℝ} (y : ℝ × ℝ) (hy : Feas P y)
    (hb : ∀ p t : ℝ, P.T ≤ p → 0 < t → payoff P qi qj (p, t) ≤ payoff P qi qj y) :
    IsGreatest (payoff P qi qj '' {x | Feas P x}) (payoff P qi qj y) := by
  refine ⟨⟨y, hy, rfl⟩, ?_⟩
  rintro _ ⟨⟨p, t⟩, ⟨hp, ht⟩, rfl⟩
  exact hb p t hp ht

end CS2Aux

open CS2Aux in
theorem solution (P : Params) (hP : P.Standing) (qi qj : ℝ)
    (hi : qi = P.qL ∨ qi = P.qH) (hj : qj = P.qL ∨ qj = P.qH)
    (hTj : P.T ≤ qj) :
    let P1s := max ((4 * qj - (1 - P.α) * qi) / 8) P.T
    let P2s := if P.T ≤ qj / 2 then qi / 2
      else if P.T < qj / (2 * (1 - P.α)) then P.T * qi / qj
      else qi / (2 * (1 - P.α))
    Feas P (P1s, P2s) ∧
      IsGreatest (payoff P qi qj '' {x | Feas P x}) (payoff P qi qj (P1s, P2s)) := by
  intro P1s P2s
  obtain ⟨hL, hLH, ha0, ha1, hT⟩ := hP
  have hqi : 0 < qi := by rcases hi with h | h <;> rw [h] <;> linarith
  have hqj : 0 < qj := by rcases hj with h | h <;> rw [h] <;> linarith
  have h1a : 0 < 1 - P.α := by linarith
  have hxle : (4 * qj - (1 - P.α) * qi) / 8 ≤ qj / 2 := by
    have : 0 ≤ (1 - P.α) * qi := mul_nonneg h1a.le hqi.le
    linarith
  by_cases h1 : P.T ≤ qj / 2
  · have hP2 : P2s = qi / 2 := if_pos h1
    have hF : Feas P (P1s, P2s) := ⟨le_max_right _ _, by rw [hP2]; linarith⟩
    refine ⟨hF, greatest_of P _ hF ?_⟩
    intro p t hp ht
    rw [hP2]
    exact reg1 P ha0 ha1 hqi hqj hT h1 p t hp ht
  · push_neg at h1
    have hP1 : P1s = P.T := max_eq_right (by linarith)
    by_cases h2 : P.T < qj / (2 * (1 - P.α))
    · have hP2 : P2s = P.T * qi / qj := by
        simp only [P2s, if_neg (not_le.2 h1), if_pos h2]
      have hF : Feas P (P1s, P2s) :=
        ⟨by rw [hP1], by rw [hP2]; positivity⟩
      refine ⟨hF, greatest_of P _ hF ?_⟩
      intro p t hp ht
      rw [hP1, hP2]
      exact reg2 P ha0 ha1 hqi hqj h1 h2 hTj p t hp ht
    · push_neg at h2
      have hP2 : P2s = qi / (2 * (1 - P.α)) := by
        simp only [P2s, if_neg (not_le.2 h1), if_neg (not_lt.2 h2)]
      have hF : Feas P (P1s, P2s) :=
        ⟨by rw [hP1], by rw [hP2]; positivity⟩
      have h2' : qj ≤ 2 * (1 - P.α) * P.T := by
        rw [div_le_iff₀ (by linarith)] at h2; linarith
      refine ⟨hF, greatest_of P _ hF ?_⟩
      intro p t hp ht
      rw [hP1, hP2]
      exact reg3 P ha0 ha1 hqi hqj h2' hTj p t hp ht
