-- Prove2me | solution 1 for CachonPushPull.Pareto.pull_survives_push_challenge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:56:11.848976+00:00
-- url     : https://prove2.me/submissions/055af523-12f3-4c14-92ea-9df5c3aff157

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits



namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

lemma cpp_F_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : ∀ x ≤ 0, cdf μ x = 0 := fun x hx =>
  le_antisymm (hD.cdf_zero ▸ (cdf μ).mono hx) (cdf_nonneg μ x)

lemma cpp_F_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : Continuous (cdf μ) := by
  have hle := cpp_F_zero μ f hD
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with h | rfl | h
  · have : (cdf μ : ℝ → ℝ) =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy using hle y hy.le
    exact continuousAt_const.congr this.symm
  · rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, (cdf μ).right_continuous 0⟩
    have : ContinuousWithinAt (fun _ => (0:ℝ)) (Set.Iic (0:ℝ)) 0 := continuousWithinAt_const
    exact this.congr (fun (y : ℝ) (hy : y ∈ Set.Iic (0:ℝ)) => hle y (Set.mem_Iic.1 hy))
      (hle 0 le_rfl)
  · exact (hD.hasDerivAt x h).continuousAt

lemma cpp_F_lt (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {a b : ℝ} (hab : a < b) (hb : 0 < b) : cdf μ a < cdf μ b := by
  rcases le_or_gt 0 a with ha | ha
  · exact hD.strictMonoOn (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb.le) hab
  · rw [cpp_F_zero μ f hD a ha.le, ← cpp_F_zero μ f hD 0 le_rfl]
    exact hD.strictMonoOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hb.le) hb

lemma cpp_F_lt_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (y : ℝ) : cdf μ y < 1 := by
  have h1 : cdf μ y < cdf μ (|y| + 1) :=
    cpp_F_lt μ f hD (by linarith [le_abs_self y]) (by positivity)
  linarith [cdf_le_one μ (|y| + 1)]

lemma cpp_F_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {x : ℝ} (hx : 0 < x) : 0 < cdf μ x := by
  have := cpp_F_lt μ f hD hx hx
  rwa [hD.cdf_zero] at this

lemma cpp_ii (μ : Measure ℝ) (a b : ℝ) :
    IntervalIntegrable (fun x => cdf μ x) volume a b :=
  (cdf μ).mono.intervalIntegrable

lemma cpp_S_sub (μ : Measure ℝ) (a b : ℝ) :
    S μ b - S μ a = (b - a) - ∫ x in a..b, cdf μ x := by
  unfold S
  rw [← intervalIntegral.integral_add_adjacent_intervals (cpp_ii μ 0 a) (cpp_ii μ a b)]
  ring

lemma cpp_S_zero (μ : Measure ℝ) : S μ 0 = 0 := by simp [S]

lemma cpp_int_le (μ : Measure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, cdf μ x) ≤ (b - a) * cdf μ b := by
  have h := intervalIntegral.integral_mono_on hab (cpp_ii μ a b)
    (intervalIntegrable_const (c := cdf μ b)) (fun x hx => (cdf μ).mono hx.2)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

lemma cpp_int_ge (μ : Measure ℝ) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * cdf μ a ≤ ∫ x in a..b, cdf μ x := by
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := cdf μ a)) (cpp_ii μ a b) (fun x hx => (cdf μ).mono hx.1)
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h

lemma cpp_int_lt (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {a b : ℝ} (hab : a < b) (hb : 0 < b) :
    (∫ x in a..b, cdf μ x) < (b - a) * cdf μ b := by
  set m := max ((a + b) / 2) (b / 2) with hm
  have ham : a < m := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hmb : m < b := max_lt (by linarith) (by linarith)
  have hm0 : 0 < m := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (cpp_ii μ a m) (cpp_ii μ m b)]
  have h1 := cpp_int_le μ ham.le
  have h2 := cpp_int_le μ hmb.le
  have h3 := cpp_F_lt μ f hD hmb (by linarith)
  nlinarith [mul_lt_mul_of_pos_left h3 (sub_pos.mpr ham)]

lemma cpp_int_gt (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) :
    (b - a) * cdf μ a < ∫ x in a..b, cdf μ x := by
  set m := (a + b) / 2 with hm
  have ham : a < m := by rw [hm]; linarith
  have hmb : m < b := by rw [hm]; linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (cpp_ii μ a m) (cpp_ii μ m b)]
  have h1 := cpp_int_ge μ ham.le
  have h2 := cpp_int_ge μ hmb.le
  have h3 := cpp_F_lt μ f hD ham (by linarith)
  nlinarith [mul_lt_mul_of_pos_left h3 (sub_pos.mpr hmb)]

lemma cpp_S_lt (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {y : ℝ} (hy : 0 < y) : S μ y < y := by
  have h := cpp_int_gt μ f hD hy le_rfl
  have e := cpp_S_sub μ 0 y
  rw [cpp_S_zero, hD.cdf_zero] at *
  linarith

lemma cpp_S_gt (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {y : ℝ} (hy : 0 < y) : y * (1 - cdf μ y) < S μ y := by
  have h := cpp_int_lt μ f hD hy hy
  have e := cpp_S_sub μ 0 y
  rw [cpp_S_zero] at e
  nlinarith

lemma cpp_S_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) {y : ℝ} (hy : 0 < y) : 0 < S μ y := by
  have := cpp_S_gt μ f hD hy
  have := cpp_F_lt_one μ f hD y
  nlinarith


lemma cpp_pullPrice_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v q : ℝ) :
    (pullPrice μ c v q - v) * (1 - cdf μ q) = c - v := by
  have h := cpp_F_lt_one μ f hD q
  have hne : 1 - cdf μ q ≠ 0 := by linarith
  unfold pullPrice
  field_simp
  ring

lemma cpp_G_diff (μ : Measure ℝ) (c v w q Q1 Q2 : ℝ)
    (hw : (w - v) * (1 - cdf μ q) = c - v) :
    ((w - v) * S μ Q2 - (c - v) * Q2) - ((w - v) * S μ Q1 - (c - v) * Q1) =
      (w - v) * ((Q2 - Q1) * cdf μ q - ∫ x in Q1..Q2, cdf μ x) := by
  have e := cpp_S_sub μ Q1 Q2
  rw [← hw]
  linear_combination (w - v) * e

lemma cpp_G_left (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v w q Q1 Q2 : ℝ) (hq : 0 < q)
    (hw : (w - v) * (1 - cdf μ q) = c - v) (hwv : 0 < w - v) (h12 : Q1 < Q2) (h2 : Q2 ≤ q) :
    (w - v) * S μ Q1 - (c - v) * Q1 < (w - v) * S μ Q2 - (c - v) * Q2 := by
  have e := cpp_G_diff μ c v w q Q1 Q2 hw
  have key : (∫ x in Q1..Q2, cdf μ x) < (Q2 - Q1) * cdf μ q := by
    rcases h2.lt_or_eq with h | h
    · have := cpp_int_le μ h12.le
      have := cpp_F_lt μ f hD h hq
      nlinarith [mul_lt_mul_of_pos_left this (sub_pos.mpr h12)]
    · subst h
      exact cpp_int_lt μ f hD h12 hq
  nlinarith [mul_pos hwv (sub_pos.mpr key)]

lemma cpp_G_right (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v w q Q1 Q2 : ℝ) (hq : 0 < q)
    (hw : (w - v) * (1 - cdf μ q) = c - v) (hwv : 0 < w - v) (h12 : Q1 < Q2) (h1 : q ≤ Q1) :
    (w - v) * S μ Q2 - (c - v) * Q2 < (w - v) * S μ Q1 - (c - v) * Q1 := by
  have e := cpp_G_diff μ c v w q Q1 Q2 hw
  have key : (Q2 - Q1) * cdf μ q < ∫ x in Q1..Q2, cdf μ x := by
    have := cpp_int_gt μ f hD h12 (by linarith)
    have := (cdf μ).mono h1
    nlinarith [mul_le_mul_of_nonneg_left this (sub_pos.mpr h12).le]
  nlinarith [mul_pos hwv (sub_pos.mpr key)]

lemma cpp_apd_eq (μ : Measure ℝ) (c v w y Q : ℝ) :
    apdSupplierProfit μ c v w w y Q = ((w - v) * S μ Q - (c - v) * Q) + (w - v) * (y - S μ y) := by
  unfold apdSupplierProfit; ring

lemma cpp_bestReply_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v q : ℝ) (hvc : v < c) (hq : 0 < q) (y Q : ℝ) :
    IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) y Q ↔ Q = max y q := by
  set w := pullPrice μ c v q with hwdef
  have hw : (w - v) * (1 - cdf μ q) = c - v := cpp_pullPrice_eq μ f hD c v q
  have hF1 := cpp_F_lt_one μ f hD q
  have hwv : 0 < w - v := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have Lle : ∀ Q1 Q2, Q1 ≤ Q2 → Q2 ≤ q →
      (w - v) * S μ Q1 - (c - v) * Q1 ≤ (w - v) * S μ Q2 - (c - v) * Q2 := by
    intro Q1 Q2 h12 h2
    rcases h12.lt_or_eq with h | h
    · exact (cpp_G_left μ f hD c v w q Q1 Q2 hq hw hwv h h2).le
    · rw [h]
  have Rle : ∀ Q1 Q2, Q1 ≤ Q2 → q ≤ Q1 →
      (w - v) * S μ Q2 - (c - v) * Q2 ≤ (w - v) * S μ Q1 - (c - v) * Q1 := by
    intro Q1 Q2 h12 h1
    rcases h12.lt_or_eq with h | h
    · exact (cpp_G_right μ f hD c v w q Q1 Q2 hq hw hwv h h1).le
    · rw [h]
  unfold IsSupplierBestReply
  simp only [cpp_apd_eq]
  constructor
  · rintro ⟨hyQ, hmax⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hQq : Q < q := by
        rcases le_total y q with h | h
        · rw [max_eq_right h] at hlt; exact hlt
        · rw [max_eq_left h] at hlt; linarith
      have := hmax q (by linarith)
      have := cpp_G_left μ f hD c v w q Q q hq hw hwv hQq le_rfl
      linarith
    · have := hmax (max y q) (le_max_left _ _)
      have := cpp_G_right μ f hD c v w q (max y q) Q hq hw hwv hgt (le_max_right _ _)
      linarith
  · rintro rfl
    refine ⟨le_max_left _ _, fun Q' hQ' => ?_⟩
    rcases le_or_gt Q' q with h | h
    · have hm : max y q = q := max_eq_right (by linarith)
      rw [hm]
      linarith [Lle Q' q h le_rfl]
    · have := Rle (max y q) Q' (max_le hQ' h.le) (le_max_right _ _)
      linarith

lemma cpp_apdR_eq (μ : Measure ℝ) (p v w y Q : ℝ) :
    apdRetailerProfit μ p v w w y Q = (p - w) * S μ Q + (w - v) * (S μ y - y) := by
  unfold apdRetailerProfit; ring

theorem pull_survives_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qP : ℝ) (hqP : 0 < qP) (hqP_eq : pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP) :
    ∀ q : ℝ, qP ≤ q →
      (∀ Q₀ : ℝ, IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀ ↔ Q₀ = q) ∧
      apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) 0 q =
        pullRetailerProfit μ p c v q ∧
      SurvivesPushChallenge μ p c v q := by
  intro q hq
  have hq0 : 0 < q := by linarith
  have hBR := cpp_bestReply_iff μ f hD c v q hvc hq0
  have hpv : 0 < p - v := by linarith
  -- key inequality at qP
  have hkey : (p - v) * (1 - cdf μ qP) ^ 2 < c - v := by
    have hu := cpp_F_lt_one μ f hD qP
    have hS := cpp_S_lt μ f hD hqP
    have hSp := cpp_S_pos μ f hD hqP
    have hne : 1 - cdf μ qP ≠ 0 := by linarith
    have e : (c - v) * S μ qP = (p - v) * (1 - cdf μ qP) ^ 2 * qP := by
      unfold pullRetailerProfit pushRetailerProfit pullRetailerProfitAt pushRetailerProfitAt
        pullPrice pushPrice at hqP_eq
      field_simp at hqP_eq
      linear_combination (-1:ℝ) * hqP_eq
    have hcv : 0 < c - v := by linarith
    nlinarith [mul_lt_mul_of_pos_left hS hcv]
  have hkq : (p - v) * (1 - cdf μ q) ^ 2 < c - v := by
    have h1 := (cdf μ).mono hq
    have h2 := cpp_F_lt_one μ f hD q
    have h3 := cpp_F_lt_one μ f hD qP
    have h4 : (1 - cdf μ q) ^ 2 ≤ (1 - cdf μ qP) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith [mul_le_mul_of_nonneg_left h4 hpv.le]
  set w := pullPrice μ c v q with hwdef
  have hw : (w - v) * (1 - cdf μ q) = c - v := cpp_pullPrice_eq μ f hD c v q
  have hF1 := cpp_F_lt_one μ f hD q
  have hwv : 0 < w - v := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hzero : apdRetailerProfit μ p v w w 0 q = pullRetailerProfit μ p c v q := by
    rw [cpp_apdR_eq, cpp_S_zero]
    simp [pullRetailerProfit, pullRetailerProfitAt, hwdef]
  refine ⟨fun Q₀ => by rw [hBR]; simp [hq0.le], hzero, ?_, ?_⟩
  · intro y _
    exact ⟨max y q, (hBR y _).mpr rfl⟩
  · intro y Q Q₀ hy hQ hQ₀
    rw [hBR] at hQ hQ₀
    rw [max_eq_right hq0.le] at hQ₀
    rw [hQ₀, hzero, hQ]
    rcases le_or_gt y q with h | h
    · rw [max_eq_right h, cpp_apdR_eq]
      have := cpp_S_lt μ f hD hy
      unfold pullRetailerProfit pullRetailerProfitAt
      rw [← hwdef]
      nlinarith
    · rw [max_eq_left h.le, cpp_apdR_eq]
      unfold pullRetailerProfit pullRetailerProfitAt
      rw [← hwdef]
      have e := cpp_S_sub μ q y
      have hb := cpp_int_ge μ h.le
      have hSq := cpp_S_lt μ f hD hq0
      -- R(y) - R(q) ≤ (y-q)[(p-v)(1-F q) - (w-v)] ≤ 0
      have hpw : (p - v) * (1 - cdf μ q) ≤ w - v := by
        have hu : 0 < 1 - cdf μ q := by linarith
        by_contra hcon
        push_neg at hcon
        have := mul_lt_mul_of_pos_right hcon hu
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hpw (sub_pos.mpr h).le, mul_le_mul_of_nonneg_left hb hpv.le]

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qP : ℝ) (hqP : 0 < qP) (hqP_eq : pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP) :
    ∀ q : ℝ, qP ≤ q →
      (∀ Q₀ : ℝ, IsSupplierBestReply μ c v (pullPrice μ c v q) (pullPrice μ c v q) 0 Q₀ ↔ Q₀ = q) ∧
      apdRetailerProfit μ p v (pullPrice μ c v q) (pullPrice μ c v q) 0 q =
        pullRetailerProfit μ p c v q ∧
      SurvivesPushChallenge μ p c v q := by
  exact pull_survives_core μ f hD p c v hvc hcp qP hqP hqP_eq
