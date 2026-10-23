-- Prove2me | solution 1 for CrowdSignal.TwoPrice.lemma_6_first
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T15:41:43.806152+00:00
-- url     : https://prove2.me/submissions/c5d5efc9-0d07-4e2b-bf8c-0aa717f40b7b

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

lemma cube_aux (u : ℝ) (h0 : 0 ≤ u) : (1 - u) * u^2 ≤ 4/27 := by
  nlinarith [mul_nonneg (sq_nonneg (3*u-2)) (by linarith : (0:ℝ) ≤ 3*u+1)]

lemma quarter (p H : ℝ) (hH : 0 < H) : (1 - p/H) * p ≤ H/4 := by
  have h3 : (1 - p/H) * p = H/4 - (p - H/2)^2/H := by field_simp; ring
  have h4 : 0 ≤ (p - H/2)^2/H := by positivity
  linarith

lemma arith3 (a H L u t : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (hL : 0 < L) (hLH : L < H)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (ht : 0 < t) (htu : t ≤ u * L) :
    (1 - u) * (1 - a) * t^2 * (1/L - 1/H) < (a^2 + 2*a + 5) * H * (H - L) / (32 * L) := by
  have hH : 0 < H := by linarith
  have ht2 : t^2 ≤ (u * L)^2 := pow_le_pow_left₀ ht.le htu 2
  have hc := cube_aux u hu0
  have h1u : 0 ≤ 1 - u := by linarith
  have hm0 : 0 ≤ (1 - u) * t^2 := by positivity
  have hm1 : (1 - u) * (1 - a) * t^2 ≤ (1 - u) * t^2 := by
    have := mul_nonneg ha0 hm0; linarith
  have hm2 : (1 - u) * t^2 ≤ (1 - u) * (u * L)^2 := mul_le_mul_of_nonneg_left ht2 h1u
  have hm3 : (1 - u) * (u * L)^2 = ((1 - u) * u^2) * L^2 := by ring
  have hm4 : ((1 - u) * u^2) * L^2 ≤ 4/27 * L^2 := mul_le_mul_of_nonneg_right hc (by positivity)
  have hLsq : L^2 < H^2 := by nlinarith
  have hpos : 0 ≤ (a^2 + 2*a)/32 * H^2 := by positivity
  have hlt : 4/27 * L^2 < (a^2 + 2*a + 5)/32 * H^2 := by nlinarith
  have hδ : 1/L - 1/H = (H - L) / (L * H) := by field_simp
  have hδpos : 0 < (H - L) / (L * H) := div_pos (by linarith) (by positivity)
  have hE : (a^2 + 2*a + 5) * H * (H - L) / (32 * L) =
      (a^2 + 2*a + 5)/32 * H^2 * ((H - L) / (L * H)) := by field_simp
  rw [hE, hδ]
  exact mul_lt_mul_of_pos_right (by linarith) hδpos

lemma arith4 (a H L p t p0 t0 K : ℝ) (hH : 0 < H) (hL : 0 < L) (hLH : L < H)
    (ht0 : H / 2 < t0) (hc : 0 < a + (1 - a) * (1 - p/H))
    (hline : 4 * p0 + (1 - a) * t0 = 2 * H)
    (hG0 : (1 - p0/H) * p0 + (a + (1 - a) * (1 - p0/H)) * (t0 - t0^2/L) = K)
    (hGx : (1 - p/H) * p + (a + (1 - a) * (1 - p/H)) * (t - t^2/L) ≤ K)
    (hne : (p, t) ≠ (p0, t0)) :
    (1 - p/H) * p + (a + (1 - a) * (1 - p/H)) * (t - t^2/H) <
      (1 - p0/H) * p0 + (a + (1 - a) * (1 - p0/H)) * (t0 - t0^2/H) := by
  have hid := lagr a H L p t p0 t0 hH.ne' hL.ne' hline
  rw [hG0] at hid
  have hA1 : 0 ≤ L * (2 * t0 - H) *
      (K - ((1 - p/H) * p + (a + (1 - a) * (1 - p/H)) * (t - t^2/L))) :=
    mul_nonneg (mul_nonneg hL.le (by linarith)) (by linarith)
  have hX : 0 ≤ 2 * t0 * (H - L) * (p - p0)^2 / H := by
    apply div_nonneg _ hH.le
    exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hY : 0 ≤ (a + (1 - a) * (1 - p/H)) * (H - L) * (t - t0)^2 :=
    mul_nonneg (mul_nonneg hc.le (by linarith)) (sq_nonneg _)
  have hpos : 0 < H * (2 * t0 - L) := mul_pos hH (by linarith)
  by_contra hcon
  push_neg at hcon
  have hprod : 0 ≤ H * (2 * t0 - L) *
    (((1 - p/H) * p + (a + (1 - a) * (1 - p/H)) * (t - t^2/H)) -
     ((1 - p0/H) * p0 + (a + (1 - a) * (1 - p0/H)) * (t0 - t0^2/H))) :=
    mul_nonneg hpos.le (by linarith)
  have hX0 : 2 * t0 * (H - L) * (p - p0)^2 / H = 0 := by linarith
  have hY0 : (a + (1 - a) * (1 - p/H)) * (H - L) * (t - t0)^2 = 0 := by linarith
  have hpp : p = p0 := by
    have : 2 * t0 * (H - L) * (p - p0)^2 = 0 := by
      rcases div_eq_zero_iff.1 hX0 with h | h
      · exact h
      · linarith
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h; linarith
  have htt : t = t0 := by
    rcases mul_eq_zero.1 hY0 with h | h
    · rcases mul_eq_zero.1 h with h | h
      · linarith
      · linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h; linarith
  exact hne (by rw [hpp, htt])

/-- The constrained maximization. -/
lemma key (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (p0 t0 : ℝ) (h2 : P.qH / 2 < t0) (hline : 4 * p0 + (1 - P.α) * t0 = 2 * P.qH)
    (hG : (1 - p0/P.qH) * p0 + (P.α + (1 - P.α) * (1 - p0/P.qH)) * (t0 - t0^2/P.qL) =
      (P.α^2 + 6*P.α + 25) * P.qL / 64)
    (p t : ℝ) (hp : 0 ≤ p) (ht : 0 < t) (hx : (p, t) ≠ (p0, t0))
    (hLH : payoff P P.qL P.qH (p, t) ≤ (P.α^2 + 6*P.α + 25) * P.qL / 64) :
    payoff P P.qH P.qH (p, t) <
      (1 - p0/P.qH) * p0 + (P.α + (1 - P.α) * (1 - p0/P.qH)) * (t0 - t0^2/P.qH) := by
  obtain ⟨hp0lt, hp0t0, ht0L, hc0pos, hK, hO, hD⟩ := dot_facts P hP hgap p0 t0 h2 hline hG
  obtain ⟨hL, hLH', ha0, ha1, hT⟩ := hP
  have hH : 0 < P.qH := by linarith
  have hEpos : 0 < (P.α^2 + 2*P.α + 5) * P.qH * (P.qH - P.qL) / (32 * P.qL) := by
    apply div_pos _ (by positivity)
    exact mul_pos (by positivity) (by linarith)
  have hKpos : 0 < (P.α^2 + 6*P.α + 25) * P.qL / 64 := by positivity
  rw [hO]
  by_cases hpH : p < P.qH
  swap
  · push_neg at hpH
    rw [payoff_zero P hH hpH]; linarith
  have hu1 : p / P.qH < 1 := (div_lt_one hH).2 hpH
  have hu0 : 0 ≤ p / P.qH := div_nonneg hp hH.le
  have hc : 0 < P.α + (1 - P.α) * (1 - p/P.qH) := by nlinarith
  by_cases htH : t < P.qH
  swap
  · push_neg at htH
    rw [payoff_A P hH hpH (by rw [mul_div_assoc, div_self hH.ne']; linarith), g_zero hH htH]
    have := quarter p P.qH hH
    linarith
  by_cases hB : t ≤ p * P.qL / P.qH
  · have hpLH : p * P.qL / P.qH ≤ p * P.qH / P.qH := by
      apply div_le_div_of_nonneg_right _ hH.le
      exact mul_le_mul_of_nonneg_left hLH'.le hp
    have hlt : p * P.qL / P.qH < P.qL := by
      rw [div_lt_iff₀ hH]
      rw [mul_comm P.qL]; exact mul_lt_mul_of_pos_right hpH hL
    have htL : t ≤ P.qL := by linarith
    rw [payoff_B P hH hpH (le_trans hB hpLH), g_eq hH htH.le]
    rw [payoff_B P hH hpH hB, g_eq hL htL] at hLH
    have hdiff : (1 - p/P.qH) * (p + P.α * t + (1 - P.α) * (t * (1 - t/P.qH))) =
        (1 - p/P.qH) * (p + P.α * t + (1 - P.α) * (t * (1 - t/P.qL))) +
          (1 - p/P.qH) * (1 - P.α) * t^2 * (1/P.qL - 1/P.qH) := by ring
    rw [hdiff]
    have htu : t ≤ p / P.qH * P.qL := by rw [div_mul_eq_mul_div]; exact hB
    have := arith3 P.α P.qH P.qL (p / P.qH) t ha0.le ha1 hL hLH' hu0 hu1 ht htu
    linarith
  · push_neg at hB
    have hle := payoff_le P ha0.le hH hH hpH ht.le
    rw [g_eq hH htH.le] at hle
    rw [payoff_A P hH hpH hB] at hLH
    have hGx : (1 - p/P.qH) * p + (P.α + (1 - P.α) * (1 - p/P.qH)) * (t - t^2/P.qL) ≤
        (P.α^2 + 6*P.α + 25) * P.qL / 64 := by
      have h' := mul_le_mul_of_nonneg_left (g_ge (q := P.qL) ht.le) hc.le
      have e : t - t^2/P.qL = t * (1 - t/P.qL) := by ring
      rw [e]; linarith
    have := arith4 P.α P.qH P.qL p t p0 t0 _ hH hL hLH' h2 hc hline hG hGx hx
    have e : t - t^2/P.qH = t * (1 - t/P.qH) := by ring
    rw [← e] at hle
    linarith

lemma devL (S c t0 ε L K : ℝ) (hL : 0 < L) (hc : 0 < c) (hε : 0 < ε) (h : L < 2 * t0)
    (hG : S + c * (t0 - t0^2/L) = K) : S + c * ((t0 + ε) * (1 - (t0 + ε)/L)) < K := by
  have e : (t0 + ε) * (1 - (t0 + ε)/L) = (t0 - t0^2/L) - ε * (2 * t0 + ε - L) / L := by
    field_simp; ring
  have hpos : 0 < ε * (2 * t0 + ε - L) / L := div_pos (mul_pos hε (by linarith)) hL
  have := mul_pos hc hpos
  rw [e]; nlinarith

lemma devH (S c t0 ε H L M gap : ℝ) (hH : 0 < H) (hL : 0 < L) (hc : 0 < c) (hε : 0 < ε)
    (hεL : ε ≤ L) (hgap : S + c * (t0 - t0^2/H) - M = gap) (hgpos : 0 < gap)
    (h3 : ε * (2 * c * (2 * t0 + L)) ≤ gap * H) :
    M < S + c * ((t0 + ε) * (1 - (t0 + ε)/H)) := by
  have e : (t0 + ε) * (1 - (t0 + ε)/H) = (t0 - t0^2/H) + (ε * (H - 2 * t0 - ε)) / H := by
    field_simp; ring
  have k1 : 0 ≤ c * ε * (H + L - ε) := mul_nonneg (mul_nonneg hc.le hε.le) (by linarith)
  have k2 : -(gap / 2) * H ≤ c * (ε * (H - 2 * t0 - ε)) := by linarith
  have k3 : -(gap / 2) ≤ c * (ε * (H - 2 * t0 - ε)) / H := by
    rw [le_div_iff₀ hH]; linarith
  have k4 : c * ((ε * (H - 2 * t0 - ε)) / H) = c * (ε * (H - 2 * t0 - ε)) / H := by ring
  rw [e, mul_add, k4]
  linarith

lemma deviate (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (p0 t0 : ℝ) (h2 : P.qH / 2 < t0) (hline : 4 * p0 + (1 - P.α) * t0 = 2 * P.qH)
    (hG : (1 - p0/P.qH) * p0 + (P.α + (1 - P.α) * (1 - p0/P.qH)) * (t0 - t0^2/P.qL) =
      (P.α^2 + 6*P.α + 25) * P.qL / 64)
    (M : ℝ)
    (hM : M < (1 - p0/P.qH) * p0 + (P.α + (1 - P.α) * (1 - p0/P.qH)) * (t0 - t0^2/P.qH)) :
    ∃ ε : ℝ, 0 < ε ∧ payoff P P.qL P.qH (p0, t0 + ε) < (P.α^2 + 6*P.α + 25) * P.qL / 64 ∧
      M < payoff P P.qH P.qH (p0, t0 + ε) := by
  obtain ⟨hp0lt, hp0t0, ht0L, hc0pos, hK, hO, hD⟩ := dot_facts P hP hgap p0 t0 h2 hline hG
  obtain ⟨hL, hLH, ha0, ha1, hT⟩ := hP
  have hH : 0 < P.qH := by linarith
  have hp0H : p0 < P.qH := by linarith
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = P.α + (1 - P.α) * (1 - p0/P.qH) := ⟨_, rfl⟩
  rw [← hc0] at hc0pos hG hM
  obtain ⟨gap, hgap'⟩ : ∃ g, (1 - p0/P.qH) * p0 + c0 * (t0 - t0^2/P.qH) - M = g := ⟨_, rfl⟩
  have hgpos : 0 < gap := by linarith
  have hden : 0 < 2 * c0 * (2 * t0 + P.qL) := by
    apply mul_pos (by linarith) (by linarith)
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min ((P.qL - t0)/2) (gap * P.qH / (2 * c0 * (2 * t0 + P.qL))) :=
    ⟨_, rfl⟩
  have hε1 : ε ≤ (P.qL - t0)/2 := hε ▸ min_le_left _ _
  have hε2 : ε ≤ gap * P.qH / (2 * c0 * (2 * t0 + P.qL)) := hε ▸ min_le_right _ _
  have hεpos : 0 < ε := by
    rw [hε]; exact lt_min (by linarith) (div_pos (mul_pos hgpos hH) hden)
  have hε3 : ε * (2 * c0 * (2 * t0 + P.qL)) ≤ gap * P.qH := by
    rwa [le_div_iff₀ hden] at hε2
  refine ⟨ε, hεpos, ?_, ?_⟩
  · have hB : p0 * P.qL / P.qH < t0 + ε := by
      rcases le_or_gt 0 p0 with hp0 | hp0
      · have : p0 * P.qL / P.qH ≤ p0 := by
          rw [div_le_iff₀ hH]; exact mul_le_mul_of_nonneg_left hLH.le hp0
        linarith
      · have : p0 * P.qL / P.qH < 0 := div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hp0 hL) hH
        linarith
    rw [payoff_A P hH hp0H hB, g_eq hL (by linarith), ← hc0]
    exact devL _ c0 t0 ε P.qL _ hL hc0pos hεpos (by linarith) hG
  · have hB : p0 * P.qH / P.qH < t0 + ε := by
      rw [mul_div_assoc, div_self hH.ne']; linarith
    rw [payoff_A P hH hp0H hB, g_eq hH (by linarith), ← hc0]
    exact devH _ c0 t0 ε P.qH P.qL M gap hH hL hc0pos hεpos (by linarith) hgap' hgpos hε3

end CS2Aux

open CS2Aux in
theorem solution (P : Params) (hP : P.Standing)
    (hgap : P.qH ≤ (P.α ^ 2 + 6 * P.α + 25) * P.qL / 16)
    (hTL : P.T ≤ (3 + P.α) / 8 * P.qL) :
    optPayoff P P.qL P.qL <
      payoff P P.qL P.qH ((3 + P.α) / 8 * P.qH, P.qH / 2) := by
  obtain ⟨_, hopt⟩ := optL P hP hTL
  obtain ⟨hL, hLH, ha0, ha1, hT⟩ := hP
  have hH : 0 < P.qH := by linarith
  rw [hopt]
  have hp : (3 + P.α) / 8 * P.qH < P.qH := by nlinarith
  have hB : (3 + P.α) / 8 * P.qH * P.qL / P.qH < P.qH / 2 := by
    have : (3 + P.α) / 8 * P.qH * P.qL / P.qH = (3 + P.α) / 8 * P.qL := by field_simp
    rw [this]; nlinarith
  have h2L : P.qH / 2 ≤ P.qL := by nlinarith
  rw [payoff_A P hH hp hB, g_eq hL h2L]
  have hid : (1 - (3 + P.α) / 8 * P.qH / P.qH) * ((3 + P.α) / 8 * P.qH) +
      (P.α + (1 - P.α) * (1 - (3 + P.α) / 8 * P.qH / P.qH)) *
        (P.qH / 2 * (1 - P.qH / 2 / P.qL)) - (P.α ^ 2 + 6 * P.α + 25) * P.qL / 64 =
      (P.qH - P.qL) * ((P.α ^ 2 + 6 * P.α + 25) * P.qL -
        2 * (P.α ^ 2 + 2 * P.α + 5) * P.qH) / (64 * P.qL) := by
    field_simp; ring
  have hf : 0 < (P.α ^ 2 + 6 * P.α + 25) * P.qL - 2 * (P.α ^ 2 + 2 * P.α + 5) * P.qH := by
    have h1 : 2 * (P.α ^ 2 + 2 * P.α + 5) * P.qH ≤
        2 * (P.α ^ 2 + 2 * P.α + 5) * ((P.α ^ 2 + 6 * P.α + 25) * P.qL / 16) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have h2 : 0 < (P.α ^ 2 + 6 * P.α + 25) * P.qL := by positivity
    have h3 : 0 < (8 - (P.α ^ 2 + 2 * P.α + 5)) := by nlinarith
    have h4 := mul_pos h2 h3
    nlinarith
  have : 0 < (P.qH - P.qL) * ((P.α ^ 2 + 6 * P.α + 25) * P.qL -
        2 * (P.α ^ 2 + 2 * P.α + 5) * P.qH) / (64 * P.qL) :=
    div_pos (mul_pos (by linarith) hf) (by positivity)
  linarith

