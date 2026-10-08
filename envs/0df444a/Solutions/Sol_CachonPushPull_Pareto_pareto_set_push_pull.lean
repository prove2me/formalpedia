-- Prove2me | solution 1 for CachonPushPull.Pareto.pareto_set_push_pull
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:09:11.010445+00:00
-- url     : https://prove2.me/submissions/584356b7-89d5-408e-b607-177c82223a18

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Contracts



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

lemma aux_jhsm_cdf_lt_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 ≤ q) : cdf μ q < 1 := by
  have h1 : cdf μ q < cdf μ (q + 1) :=
    hD.strictMonoOn (Set.mem_Ici.mpr hq) (Set.mem_Ici.mpr (by linarith)) (by linarith)
  linarith [cdf_le_one μ (q + 1)]

lemma aux_jhsm_f_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (x : ℝ) (hx : 0 < x) : 0 ≤ f x :=
  (hD.hasDerivAt x hx).nonneg_of_monotone (monotone_cdf μ)

lemma aux_jhsm_g_strictMonoOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) :
    StrictMonoOn (fun y : ℝ => y * f y / (1 - cdf μ y)) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    have hx' : (0 : ℝ) < x := hx
    have hne : deriv (fun y : ℝ => y * f y / (1 - cdf μ y)) x ≠ 0 := (hD.igfr x hx').ne'
    exact (differentiableAt_of_deriv_ne_zero hne).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact hD.igfr x hx

lemma aux_jhsm_S_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) (hq : 0 < q) :
    S μ q = q * ∫ t in (0 : ℝ)..1, (1 - cdf μ (q * t)) := by
  have hint : IntervalIntegrable (cdf μ) volume 0 q := (monotone_cdf μ).intervalIntegrable
  have h1 : ∫ x in (0 : ℝ)..q, (1 - cdf μ x) = q - ∫ x in (0 : ℝ)..q, cdf μ x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hint]
    simp
  have h2 : ∫ t in (0 : ℝ)..1, (1 - cdf μ (q * t)) =
      q⁻¹ • ∫ x in q * 0..q * 1, (1 - cdf μ x) :=
    intervalIntegral.integral_comp_mul_left (fun x => 1 - cdf μ x) hq.ne'
  rw [h2, mul_zero, mul_one, h1, smul_eq_mul, S]
  field_simp

lemma aux_jhsm_ratio_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    MonotoneOn (fun q : ℝ => (1 - cdf μ (t * q)) / (1 - cdf μ q)) (Set.Ioi 0) := by
  have hderiv : ∀ q : ℝ, 0 < q → HasDerivAt (fun q : ℝ => (1 - cdf μ (t * q)) / (1 - cdf μ q))
      (((0 - f (t * q)) * (t * 1) * (1 - cdf μ q) - (1 - cdf μ (t * q)) * (0 - f q))
        / (1 - cdf μ q) ^ 2) q := by
    intro q hq
    have htq : 0 < t * q := mul_pos ht0 hq
    have hA : HasDerivAt (fun q : ℝ => 1 - cdf μ (t * q)) ((0 - f (t * q)) * (t * 1)) q := by
      have := ((hasDerivAt_const (t * q) (1 : ℝ)).sub (hD.hasDerivAt (t * q) htq)).comp q
        ((hasDerivAt_id q).const_mul t)
      simpa [Function.comp_def] using this
    have hB : HasDerivAt (fun q : ℝ => 1 - cdf μ q) (0 - f q) q :=
      (hasDerivAt_const q (1 : ℝ)).sub (hD.hasDerivAt q hq)
    have hne : (1 - cdf μ q) ≠ 0 := by
      have := aux_jhsm_cdf_lt_one μ f hD q hq.le
      linarith
    exact hA.div hB hne
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro q hq
    exact (hderiv q hq).continuousAt.continuousWithinAt
  · intro q hq
    rw [interior_Ioi] at hq
    exact (hderiv q hq).differentiableAt.differentiableWithinAt
  · intro q hq
    rw [interior_Ioi] at hq
    have hq' : (0 : ℝ) < q := hq
    rw [(hderiv q hq').deriv]
    apply div_nonneg _ (sq_nonneg _)
    have htq : 0 < t * q := mul_pos ht0 hq'
    have hu : 0 < 1 - cdf μ q := by
      have := aux_jhsm_cdf_lt_one μ f hD q hq'.le
      linarith
    have hut : 0 < 1 - cdf μ (t * q) := by
      have := aux_jhsm_cdf_lt_one μ f hD (t * q) htq.le
      linarith
    have hg : (t * q) * f (t * q) / (1 - cdf μ (t * q)) ≤ q * f q / (1 - cdf μ q) :=
      (aux_jhsm_g_strictMonoOn μ f hD).monotoneOn htq hq'
        (by nlinarith)
    rw [div_le_div_iff₀ hut hu] at hg
    -- hg : t*q*f(tq)*(1-F q) ≤ q * f q * (1 - F(tq))
    have key : t * f (t * q) * (1 - cdf μ q) ≤ f q * (1 - cdf μ (t * q)) := by
      have h' : q * (t * f (t * q) * (1 - cdf μ q)) ≤ q * (f q * (1 - cdf μ (t * q))) := by
        nlinarith
      exact le_of_mul_le_mul_left h' hq'
    nlinarith

lemma aux_jhsm_R_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 < q) :
    S μ q / (q * (1 - cdf μ q)) =
      ∫ t in (0 : ℝ)..1, (1 - cdf μ (q * t)) / (1 - cdf μ q) := by
  have hu : 0 < 1 - cdf μ q := by
    have := aux_jhsm_cdf_lt_one μ f hD q hq.le
    linarith
  rw [intervalIntegral.integral_div, aux_jhsm_S_eq μ q hq]
  field_simp

lemma aux_jhsm_int_ok (μ : Measure ℝ) [IsProbabilityMeasure μ] (q : ℝ) (hq : 0 ≤ q) :
    IntervalIntegrable (fun t => (1 - cdf μ (q * t)) / (1 - cdf μ q)) volume 0 1 := by
  have hanti : Antitone (fun t => 1 - cdf μ (q * t)) := by
    intro a b hab
    have : cdf μ (q * a) ≤ cdf μ (q * b) :=
      monotone_cdf μ (mul_le_mul_of_nonneg_left hab hq)
    simp only
    linarith
  exact hanti.intervalIntegrable.div_const _

lemma aux_jhsm_R_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    S μ a / (a * (1 - cdf μ a)) ≤ S μ b / (b * (1 - cdf μ b)) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [aux_jhsm_R_eq μ f hD a ha, aux_jhsm_R_eq μ f hD b hb]
  apply intervalIntegral.integral_mono_on zero_le_one (aux_jhsm_int_ok μ a ha.le)
    (aux_jhsm_int_ok μ b hb.le)
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    simp only [mul_zero]
    have hua : 0 < 1 - cdf μ a := by
      have := aux_jhsm_cdf_lt_one μ f hD a ha.le
      linarith
    have hub : 0 < 1 - cdf μ b := by
      have := aux_jhsm_cdf_lt_one μ f hD b hb.le
      linarith
    have hmono : cdf μ a ≤ cdf μ b := monotone_cdf μ hab
    have h1 : 0 ≤ 1 - cdf μ 0 := by linarith [cdf_le_one μ 0]
    exact div_le_div_of_nonneg_left h1 hub (by linarith)
  · have := aux_jhsm_ratio_mono μ f hD t h0 ht.2 ha hb hab
    simpa [mul_comm] using this

lemma aux_jhsm_R_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (b : ℝ) (hb : 0 < b) :
    0 < S μ b / (b * (1 - cdf μ b)) := by
  have hub : 0 < 1 - cdf μ b := by
    have := aux_jhsm_cdf_lt_one μ f hD b hb.le
    linarith
  have h1 : ∫ t in (0 : ℝ)..1, (1 : ℝ) ≤
      ∫ t in (0 : ℝ)..1, (1 - cdf μ (b * t)) / (1 - cdf μ b) := by
    apply intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
      (aux_jhsm_int_ok μ b hb.le)
    intro t ht
    rw [le_div_iff₀ hub, one_mul]
    have : cdf μ (b * t) ≤ cdf μ b := by
      apply monotone_cdf μ
      nlinarith [ht.1, ht.2]
    linarith
  rw [aux_jhsm_R_eq μ f hD b hb]
  rw [intervalIntegral.integral_const] at h1
  simp only [sub_zero, smul_eq_mul, mul_one] at h1
  linarith

theorem cpp_jh_smono (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) :
    StrictMonoOn (fun q : ℝ => j μ q * hazard μ f q) (Set.Ioi 0) := by
  have hform : ∀ q : ℝ, 0 < q → j μ q * hazard μ f q =
      (S μ q / (q * (1 - cdf μ q))) * (q * f q / (1 - cdf μ q)) := by
    intro q hq
    have hu : 0 < 1 - cdf μ q := by
      have := aux_jhsm_cdf_lt_one μ f hD q hq.le
      linarith
    simp only [j, hazard]
    field_simp
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  simp only
  rw [hform a ha', hform b hb']
  have hR := aux_jhsm_R_mono μ f hD a b ha' hab.le
  have hRpos := aux_jhsm_R_pos μ f hD b hb'
  have hg : a * f a / (1 - cdf μ a) < b * f b / (1 - cdf μ b) :=
    aux_jhsm_g_strictMonoOn μ f hD ha hb hab
  have hga : 0 ≤ a * f a / (1 - cdf μ a) := by
    have hua : 0 < 1 - cdf μ a := by
      have := aux_jhsm_cdf_lt_one μ f hD a ha'.le
      linarith
    exact div_nonneg (mul_nonneg ha'.le (aux_jhsm_f_nonneg μ f hD a ha')) hua.le
  calc (S μ a / (a * (1 - cdf μ a))) * (a * f a / (1 - cdf μ a))
      ≤ (S μ b / (b * (1 - cdf μ b))) * (a * f a / (1 - cdf μ a)) :=
        mul_le_mul_of_nonneg_right hR hga
    _ < (S μ b / (b * (1 - cdf μ b))) * (b * f b / (1 - cdf μ b)) :=
        mul_lt_mul_of_pos_left hg hRpos

lemma cpp_u_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) : 0 < 1 - cdf μ q := by
  linarith [cpp_F_lt_one μ f hD q]

lemma cpp_pr_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v q : ℝ) :
    pullRetailerProfit μ p c v q = ((p - c) - (p - v) * cdf μ q) * S μ q / (1 - cdf μ q) := by
  have hu := (cpp_u_pos μ f hD q).ne'
  unfold pullRetailerProfit pullRetailerProfitAt pullPrice
  field_simp
  ring

lemma cpp_ps_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v q : ℝ) :
    pullSupplierProfit μ c v q = (c - v) * (S μ q / (1 - cdf μ q) - q) := by
  have hu := (cpp_u_pos μ f hD q).ne'
  unfold pullSupplierProfit pullSupplierProfitAt pullPrice
  field_simp
  ring

lemma cpp_hr_eq (μ : Measure ℝ) (p v q : ℝ) :
    pushRetailerProfit μ p v q = (p - v) * (S μ q - (1 - cdf μ q) * q) := by
  unfold pushRetailerProfit pushRetailerProfitAt pushPrice; ring

lemma cpp_hs_eq (μ : Measure ℝ) (p c v q : ℝ) :
    pushSupplierProfit μ p c v q = ((p - c) - (p - v) * cdf μ q) * q := by
  unfold pushSupplierProfit pushSupplierProfitAt pushPrice; ring

lemma cpp_sum_pull (μ : Measure ℝ) (p c v q : ℝ) :
    pullRetailerProfit μ p c v q + pullSupplierProfit μ c v q = chainProfit μ p c v q := by
  unfold pullRetailerProfit pullRetailerProfitAt pullSupplierProfit pullSupplierProfitAt chainProfit
  ring

lemma cpp_sum_push (μ : Measure ℝ) (p c v q : ℝ) :
    pushRetailerProfit μ p v q + pushSupplierProfit μ p c v q = chainProfit μ p c v q := by
  unfold pushRetailerProfit pushRetailerProfitAt pushSupplierProfit pushSupplierProfitAt chainProfit
  ring

/-- `π_r - π̂_r = Kf / u`. -/
lemma cpp_E_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v q : ℝ) :
    pullRetailerProfit μ p c v q - pushRetailerProfit μ p v q =
      ((p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q) / (1 - cdf μ q) := by
  have hu := (cpp_u_pos μ f hD q).ne'
  rw [cpp_pr_eq μ f hD, cpp_hr_eq]
  field_simp
  ring

lemma cpp_S_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) : HasDerivAt (S μ) (1 - cdf μ q) q := by
  have h1 : HasDerivAt (fun q => ∫ x in (0:ℝ)..q, cdf μ x) (cdf μ q) q :=
    ((cpp_F_cont μ f hD).integral_hasStrictDerivAt 0 q).hasDerivAt
  unfold S
  exact (hasDerivAt_id' q).sub h1

lemma cpp_S_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : Continuous (S μ) :=
  continuous_iff_continuousAt.mpr fun q => (cpp_S_deriv μ f hD q).continuousAt

lemma cpp_chain_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v q : ℝ) :
    HasDerivAt (chainProfit μ p c v) ((p - v) * (1 - cdf μ q) - (c - v)) q := by
  have h3 := ((cpp_S_deriv μ f hD q).const_mul (p - v)).sub ((hasDerivAt_id' q).const_mul (c - v))
  have he : chainProfit μ p c v = fun q => (p - v) * S μ q - (c - v) * q := rfl
  rw [he]
  exact h3.congr_deriv (by ring)

lemma cpp_hr_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p v q : ℝ) (hq : 0 < q) :
    HasDerivAt (pushRetailerProfit μ p v) ((p - v) * f q * q) q := by
  have hF := hD.hasDerivAt q hq
  have h := ((cpp_S_deriv μ f hD q).sub ((hF.const_sub 1).mul (hasDerivAt_id' q))).const_mul (p - v)
  have he : pushRetailerProfit μ p v = fun q => (p - v) * (S μ q - (1 - cdf μ q) * q) := by
    funext x; exact cpp_hr_eq μ p v x
  rw [he]
  exact h.congr_deriv (by simp; ring)

lemma cpp_jS_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 < q) :
    HasDerivAt (fun x => S μ x / (1 - cdf μ x)) (1 + S μ q * f q / (1 - cdf μ q) ^ 2) q := by
  have hF := hD.hasDerivAt q hq
  have hu := (cpp_u_pos μ f hD q).ne'
  have h := (cpp_S_deriv μ f hD q).div (hF.const_sub 1) hu
  refine h.congr_deriv ?_
  field_simp
  ring

lemma cpp_ps_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v q : ℝ) (hq : 0 < q) :
    HasDerivAt (pullSupplierProfit μ c v) ((c - v) * (S μ q * f q / (1 - cdf μ q) ^ 2)) q := by
  have h := ((cpp_jS_deriv μ f hD q hq).sub (hasDerivAt_id' q)).const_mul (c - v)
  have he : pullSupplierProfit μ c v = fun q => (c - v) * (S μ q / (1 - cdf μ q) - q) := by
    funext x; exact cpp_ps_eq μ f hD c v x
  rw [he]
  exact h.congr_deriv (by ring)

lemma cpp_pr_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v q : ℝ) (hq : 0 < q) :
    HasDerivAt (pullRetailerProfit μ p c v)
      ((p - v) * (1 - cdf μ q) - (c - v) - (c - v) * (S μ q * f q / (1 - cdf μ q) ^ 2)) q := by
  have h := (cpp_chain_deriv μ f hD p c v q).sub (cpp_ps_deriv μ f hD c v q hq)
  have he : pullRetailerProfit μ p c v = fun q => chainProfit μ p c v q - pullSupplierProfit μ c v q := by
    funext x; rw [← cpp_sum_pull]; ring
  rw [he]
  exact h

lemma cpp_hs_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v q : ℝ) (hq : 0 < q) :
    HasDerivAt (pushSupplierProfit μ p c v)
      ((p - v) * (1 - cdf μ q) - (c - v) - (p - v) * f q * q) q := by
  have h := (cpp_chain_deriv μ f hD p c v q).sub (cpp_hr_deriv μ f hD p v q hq)
  have he : pushSupplierProfit μ p c v = fun q => chainProfit μ p c v q - pushRetailerProfit μ p v q := by
    funext x; rw [← cpp_sum_push]; ring
  rw [he]
  exact h

lemma cpp_jh_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) :
    j μ q * hazard μ f q = S μ q * f q / (1 - cdf μ q) ^ 2 := by
  have hu := (cpp_u_pos μ f hD q).ne'
  simp only [j, hazard]
  field_simp

lemma cpp_j_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : Continuous (fun x => S μ x / (1 - cdf μ x)) :=
  (cpp_S_cont μ f hD).div (continuous_const.sub (cpp_F_cont μ f hD))
    (fun x => (cpp_u_pos μ f hD x).ne')

/-- Fact A: `u S - u^2 q < q S f`. -/
lemma cpp_factA (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 < q) :
    (1 - cdf μ q) * S μ q - (1 - cdf μ q) ^ 2 * q < q * S μ q * f q := by
  set K := S μ q * f q / (1 - cdf μ q) ^ 2 with hK
  let φ : ℝ → ℝ := fun x => S μ x / (1 - cdf μ x) - x - x * K
  have hanti : StrictAntiOn φ (Set.Icc 0 q) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 q)
    · exact (((cpp_j_cont μ f hD).sub continuous_id).sub (continuous_id.mul continuous_const)).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hd : HasDerivAt φ (1 + S μ x * f x / (1 - cdf μ x) ^ 2 - 1 - 1 * K) x :=
        ((cpp_jS_deriv μ f hD x hx.1).sub (hasDerivAt_id' x)).sub
        ((hasDerivAt_id' x).mul_const K)
      rw [hd.deriv]
      have hlt := cpp_jh_smono μ f hD (Set.mem_Ioi.mpr hx.1) (Set.mem_Ioi.mpr hq) hx.2
      simp only at hlt
      rw [cpp_jh_eq μ f hD, cpp_jh_eq μ f hD] at hlt
      rw [hK]
      linarith
  have h := hanti (Set.left_mem_Icc.mpr hq.le) (Set.right_mem_Icc.mpr hq.le) hq
  simp only [φ, cpp_S_zero, hD.cdf_zero] at h
  have hu := cpp_u_pos μ f hD q
  have e : S μ q / (1 - cdf μ q) * (1 - cdf μ q) ^ 2 = (1 - cdf μ q) * S μ q := by
    field_simp
  have e2 : K * (1 - cdf μ q) ^ 2 = S μ q * f q := by
    rw [hK]; field_simp
  have hu2 : 0 < (1 - cdf μ q) ^ 2 := by positivity
  have := mul_lt_mul_of_pos_right (show S μ q / (1 - cdf μ q) - q - q * K < 0 by linarith) hu2
  nlinarith


lemma cpp_exists_qo (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ∃ qo : ℝ, 0 < qo ∧ cdf μ qo = (p - c) / (p - v) := by
  have hpv : 0 < p - v := by linarith
  have ha0 : 0 < (p - c) / (p - v) := div_pos (by linarith) hpv
  have ha1 : (p - c) / (p - v) < 1 := by rw [div_lt_one hpv]; linarith
  obtain ⟨M, hM⟩ := ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds ha1)).exists_forall_of_atTop
  have hM1 := hM (max M 1) (le_max_left _ _)
  have hsub := intermediate_value_Icc (show (0:ℝ) ≤ max M 1 by positivity)
    (cpp_F_cont μ f hD).continuousOn
  obtain ⟨x, hx, hFx⟩ := hsub ⟨by rw [hD.cdf_zero]; exact ha0.le, hM1.le⟩
  refine ⟨x, ?_, hFx⟩
  rcases hx.1.lt_or_eq with h | h
  · exact h
  · rw [← h, hD.cdf_zero] at hFx; linarith

/-- `ψ(q) = (1-F)^2 q / S`. -/
noncomputable def cppPsi (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (1 - cdf μ x) * (1 - cdf μ x) * x / S μ x

lemma cpp_psi_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (q : ℝ) (hq : 0 < q) :
    HasDerivAt (cppPsi μ)
      ((1 - cdf μ q) * ((1 - cdf μ q) * S μ q - (1 - cdf μ q) ^ 2 * q - 2 * f q * q * S μ q)
        / S μ q ^ 2) q := by
  have hF := (hD.hasDerivAt q hq).const_sub 1
  have hS := cpp_S_deriv μ f hD q
  have hSp := (cpp_S_pos μ f hD hq).ne'
  have h : HasDerivAt (fun x => (1 - cdf μ x) * (1 - cdf μ x) * x / S μ x)
      ((((-f q * (1 - cdf μ q) + (1 - cdf μ q) * -f q) * q + (1 - cdf μ q) * (1 - cdf μ q) * 1)
        * S μ q - (1 - cdf μ q) * (1 - cdf μ q) * q * (1 - cdf μ q)) / S μ q ^ 2) q :=
    ((hF.mul hF).mul (hasDerivAt_id' q)).div hS hSp
  unfold cppPsi
  refine h.congr_deriv ?_
  field_simp
  ring

lemma cpp_psi_anti (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : StrictAntiOn (cppPsi μ) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (cpp_psi_deriv μ f hD x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : (0:ℝ) < x := hx
    rw [(cpp_psi_deriv μ f hD x hx').deriv]
    have hA := cpp_factA μ f hD x hx'
    have hf := aux_jhsm_f_nonneg μ f hD x hx'
    have hS := cpp_S_pos μ f hD hx'
    have hu := cpp_u_pos μ f hD x
    apply div_neg_of_neg_of_pos _ (by positivity)
    apply mul_neg_of_pos_of_neg hu
    nlinarith [mul_nonneg (mul_nonneg hf hx'.le) hS.le]

lemma cpp_psi_contOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : ContinuousOn (cppPsi μ) (Set.Ioi 0) :=
  fun x hx => (cpp_psi_deriv μ f hD x hx).continuousAt.continuousWithinAt

lemma cpp_qP_exists (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo0 : 0 < qo) (hqo : cdf μ qo = (p - c) / (p - v)) :
    ∃ qP : ℝ, 0 < qP ∧ qP < qo ∧ (p - v) * cppPsi μ qP = c - v := by
  have hpv : 0 < p - v := by linarith
  set a := (p - c) / (p - v) with ha
  have ha0 : 0 < a := div_pos (by linarith) hpv
  have ha1 : a < 1 := by rw [ha, div_lt_one hpv]; linarith
  have hb : (c - v) / (p - v) = 1 - a := by rw [ha]; field_simp; ring
  -- q1 with F q1 = a/2
  obtain ⟨q1, hq1, hFq1⟩ := intermediate_value_Icc hqo0.le (cpp_F_cont μ f hD).continuousOn
    (show a / 2 ∈ Set.Icc (cdf μ 0) (cdf μ qo) from ⟨by rw [hD.cdf_zero]; linarith, by
      rw [hqo]; linarith⟩)
  have hq1pos : 0 < q1 := by
    rcases hq1.1.lt_or_eq with h | h
    · exact h
    · rw [← h, hD.cdf_zero] at hFq1; linarith
  have hq1lt : q1 < qo := by
    rcases hq1.2.lt_or_eq with h | h
    · exact h
    · rw [h, hqo] at hFq1; linarith
  have hpsi1 : 1 - a < cppPsi μ q1 := by
    unfold cppPsi
    have hS := cpp_S_pos μ f hD hq1pos
    have hSl := cpp_S_lt μ f hD hq1pos
    rw [lt_div_iff₀ hS, hFq1]
    have e1 : 1 - a < (1 - a / 2) * (1 - a / 2) := by nlinarith
    have e2 := mul_lt_mul_of_pos_right e1 hS
    have e3 := mul_lt_mul_of_pos_left hSl (show 0 < (1 - a / 2) * (1 - a / 2) by nlinarith)
    linarith
  have hpsio : cppPsi μ qo < 1 - a := by
    unfold cppPsi
    have hS := cpp_S_pos μ f hD hqo0
    have hSg := cpp_S_gt μ f hD hqo0
    rw [div_lt_iff₀ hS, hqo]
    rw [hqo] at hSg
    nlinarith [mul_lt_mul_of_pos_left hSg (show 0 < 1 - a by linarith)]
  obtain ⟨qP, hqP, hψ⟩ := intermediate_value_Icc' hq1lt.le
    ((cpp_psi_contOn μ f hD).mono (fun x hx => lt_of_lt_of_le hq1pos hx.1))
    (show 1 - a ∈ Set.Icc (cppPsi μ qo) (cppPsi μ q1) from ⟨hpsio.le, hpsi1.le⟩)
  refine ⟨qP, lt_of_lt_of_le hq1pos hqP.1, ?_, ?_⟩
  · rcases hqP.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hψ; linarith
  · rw [hψ, ← hb]; field_simp

/-- sign function `Kf(q) = (p-v) u^2 q - (c-v) S`. -/
lemma cpp_Kf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v q : ℝ) (hq : 0 < q) :
    (p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q = S μ q * ((p - v) * cppPsi μ q - (c - v)) := by
  have hS := (cpp_S_pos μ f hD hq).ne'
  unfold cppPsi
  field_simp

lemma cpp_Kf_sign (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qP : ℝ) (hqP : 0 < qP) (hψ : (p - v) * cppPsi μ qP = c - v) (q : ℝ) (hq : 0 < q) :
    (q < qP → 0 < (p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q) ∧
    (q = qP → (p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q = 0) ∧
    (qP < q → (p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q < 0) := by
  have hpv : 0 < p - v := by linarith
  rw [cpp_Kf_eq μ f hD p c v q hq]
  have hS := cpp_S_pos μ f hD hq
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := cpp_psi_anti μ f hD (Set.mem_Ioi.mpr hq) (Set.mem_Ioi.mpr hqP) h
    apply mul_pos hS
    nlinarith [mul_lt_mul_of_pos_left this hpv]
  · rw [h, hψ]; ring
  · have := cpp_psi_anti μ f hD (Set.mem_Ioi.mpr hqP) (Set.mem_Ioi.mpr hq) h
    apply mul_neg_of_pos_of_neg hS
    nlinarith [mul_lt_mul_of_pos_left this hpv]


lemma cpp_f_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (x : ℝ) (hx : 0 < x) : 0 < f x := by
  have h := aux_jhsm_g_strictMonoOn μ f hD (Set.mem_Ioi.mpr (by linarith : (0:ℝ) < x / 2))
    (Set.mem_Ioi.mpr hx) (by linarith)
  simp only at h
  have h1 := cpp_u_pos μ f hD (x / 2)
  have h2 := cpp_u_pos μ f hD x
  have h3 := aux_jhsm_f_nonneg μ f hD (x / 2) (by linarith)
  have h4 : 0 ≤ x / 2 * f (x / 2) / (1 - cdf μ (x / 2)) := by positivity
  have h5 : 0 < x * f x / (1 - cdf μ x) := by linarith
  have h6 : 0 < x * f x := by
    by_contra hc; push_neg at hc
    have : x * f x / (1 - cdf μ x) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc h2.le
    linarith
  by_contra hc; push_neg at hc
  nlinarith

lemma cpp_pr_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) : Continuous (pullRetailerProfit μ p c v) := by
  have he : pullRetailerProfit μ p c v =
      fun q => ((p - c) - (p - v) * cdf μ q) * S μ q / (1 - cdf μ q) := by
    funext x; exact cpp_pr_eq μ f hD p c v x
  rw [he]
  have hF := cpp_F_cont μ f hD
  exact ((continuous_const.sub (continuous_const.mul hF)).mul (cpp_S_cont μ f hD)).div
    (continuous_const.sub hF) (fun x => (cpp_u_pos μ f hD x).ne')

lemma cpp_ps_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v : ℝ) : Continuous (pullSupplierProfit μ c v) := by
  have he : pullSupplierProfit μ c v = fun q => (c - v) * (S μ q / (1 - cdf μ q) - q) := by
    funext x; exact cpp_ps_eq μ f hD c v x
  rw [he]
  exact continuous_const.mul ((cpp_j_cont μ f hD).sub continuous_id)

lemma cpp_hs_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) : Continuous (pushSupplierProfit μ p c v) := by
  have he : pushSupplierProfit μ p c v = fun q => ((p - c) - (p - v) * cdf μ q) * q := by
    funext x; exact cpp_hs_eq μ p c v x
  rw [he]
  exact (continuous_const.sub (continuous_const.mul (cpp_F_cont μ f hD))).mul continuous_id

lemma cpp_hr_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p v : ℝ) : Continuous (pushRetailerProfit μ p v) := by
  have he : pushRetailerProfit μ p v = fun q => (p - v) * (S μ q - (1 - cdf μ q) * q) := by
    funext x; exact cpp_hr_eq μ p v x
  rw [he]
  exact continuous_const.mul ((cpp_S_cont μ f hD).sub
    ((continuous_const.sub (cpp_F_cont μ f hD)).mul continuous_id))

lemma cpp_chain_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) : Continuous (chainProfit μ p c v) :=
  continuous_iff_continuousAt.mpr fun q => (cpp_chain_deriv μ f hD p c v q).continuousAt

lemma cpp_chain_smono (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo0 : 0 < qo) (hqo : cdf μ qo = (p - c) / (p - v)) :
    StrictMonoOn (chainProfit μ p c v) (Set.Icc 0 qo) := by
  have hpv : 0 < p - v := by linarith
  have e : (p - v) * cdf μ qo = p - c := by rw [hqo]; field_simp
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 qo) (cpp_chain_cont μ f hD p c v).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(cpp_chain_deriv μ f hD p c v x).deriv]
  have := cpp_F_lt μ f hD hx.2 hqo0
  nlinarith

lemma cpp_N_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo0 : 0 < qo) (hqo : cdf μ qo = (p - c) / (p - v)) (q : ℝ) (hq : q < qo) :
    0 < (p - c) - (p - v) * cdf μ q := by
  have hpv : 0 < p - v := by linarith
  have e : (p - v) * cdf μ qo = p - c := by rw [hqo]; field_simp
  have := cpp_F_lt μ f hD hq hqo0
  nlinarith

lemma cpp_lt_qo (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) (q : ℝ)
    (hN : 0 < (p - c) - (p - v) * cdf μ q) : q < qo := by
  have hpv : 0 < p - v := by linarith
  have e : (p - v) * cdf μ qo = p - c := by rw [hqo]; field_simp
  by_contra h; push_neg at h
  have := (cdf μ).mono h
  nlinarith

lemma cpp_le_qo (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo0 : 0 < qo) (hqo : cdf μ qo = (p - c) / (p - v)) (q : ℝ)
    (hN : 0 ≤ (p - c) - (p - v) * cdf μ q) : q ≤ qo := by
  have hpv : 0 < p - v := by linarith
  have e : (p - v) * cdf μ qo = p - c := by rw [hqo]; field_simp
  by_contra h; push_neg at h
  have := cpp_F_lt μ f hD h (by linarith)
  nlinarith

/-- derivative of `π_r` is strictly decreasing. -/
lemma cpp_prd_anti (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) {x y : ℝ} (hx : 0 < x)
    (hxy : x < y) :
    (p - v) * (1 - cdf μ y) - (c - v) - (c - v) * (S μ y * f y / (1 - cdf μ y) ^ 2) <
      (p - v) * (1 - cdf μ x) - (c - v) - (c - v) * (S μ x * f x / (1 - cdf μ x) ^ 2) := by
  have h1 := cpp_jh_smono μ f hD (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr (by linarith)) hxy
  simp only at h1
  rw [cpp_jh_eq μ f hD, cpp_jh_eq μ f hD] at h1
  have h2 := cpp_F_lt μ f hD hxy (by linarith)
  have hpv : 0 < p - v := by linarith
  have hcv : 0 < c - v := by linarith
  nlinarith [mul_lt_mul_of_pos_left h1 hcv, mul_lt_mul_of_pos_left h2 hpv]

lemma cpp_prd_neg_qP (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) (qP : ℝ) (hqP : 0 < qP)
    (hK : (p - v) * (1 - cdf μ qP) ^ 2 * qP - (c - v) * S μ qP = 0) :
    (p - v) * (1 - cdf μ qP) - (c - v) - (c - v) * (S μ qP * f qP / (1 - cdf μ qP) ^ 2) < 0 := by
  have hA := cpp_factA μ f hD qP hqP
  have hu := cpp_u_pos μ f hD qP
  have hS := cpp_S_pos μ f hD hqP
  have hpv : 0 < p - v := by linarith
  set u := 1 - cdf μ qP
  have hu2 : 0 < u ^ 2 := by positivity
  have key : ((p - v) * u - (c - v) - (c - v) * (S μ qP * f qP / u ^ 2)) * (u ^ 2 * S μ qP) =
      (p - v) * u ^ 2 * (u * S μ qP - u ^ 2 * qP - qP * S μ qP * f qP) := by
    have e : (c - v) * S μ qP = (p - v) * u ^ 2 * qP := by linarith
    field_simp
    linear_combination (-(u ^ 2) - S μ qP * f qP) * e
  have : ((p - v) * u - (c - v) - (c - v) * (S μ qP * f qP / u ^ 2)) * (u ^ 2 * S μ qP) < 0 := by
    rw [key]
    apply mul_neg_of_pos_of_neg (by positivity)
    linarith
  exact neg_of_mul_neg_left this (by positivity)

lemma cpp_hsd_neg_qP (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) (qP : ℝ) (hqP : 0 < qP)
    (hK : (p - v) * (1 - cdf μ qP) ^ 2 * qP - (c - v) * S μ qP = 0) :
    (p - v) * (1 - cdf μ qP) - (c - v) < (p - v) * f qP * qP := by
  have hA := cpp_factA μ f hD qP hqP
  have hu := cpp_u_pos μ f hD qP
  have hS := cpp_S_pos μ f hD hqP
  have hpv : 0 < p - v := by linarith
  set u := 1 - cdf μ qP
  have key : ((p - v) * u - (c - v)) * S μ qP = (p - v) * (u * S μ qP - u ^ 2 * qP) := by
    linear_combination hK
  have : ((p - v) * u - (c - v)) * S μ qP < ((p - v) * f qP * qP) * S μ qP := by
    rw [key]
    nlinarith [mul_lt_mul_of_pos_left hA hpv]
  exact lt_of_mul_lt_mul_right this hS.le

lemma cpp_pr_anti_after (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) (qP : ℝ) (hqP : 0 < qP)
    (hK : (p - v) * (1 - cdf μ qP) ^ 2 * qP - (c - v) * S μ qP = 0) :
    StrictAntiOn (pullRetailerProfit μ p c v) (Set.Ici qP) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici qP) (cpp_pr_cont μ f hD p c v).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx' : qP < x := hx
  rw [(cpp_pr_deriv μ f hD p c v x (by linarith)).deriv]
  have := cpp_prd_anti μ f hD p c v hvc hcp hqP hx'
  have := cpp_prd_neg_qP μ f hD p c v hvc hcp qP hqP hK
  linarith

lemma cpp_hs_anti_after (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) (qP : ℝ) (hqP : 0 < qP)
    (hK : (p - v) * (1 - cdf μ qP) ^ 2 * qP - (c - v) * S μ qP = 0) :
    StrictAntiOn (pushSupplierProfit μ p c v) (Set.Ici qP) := by
  have hpv : 0 < p - v := by linarith
  have hcv : 0 < c - v := by linarith
  have h0 := cpp_hsd_neg_qP μ f hD p c v hvc hcp qP hqP hK
  apply strictAntiOn_of_deriv_neg (convex_Ici qP) (cpp_hs_cont μ f hD p c v).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  have hx' : qP < x := hx
  have hx0 : 0 < x := by linarith
  rw [(cpp_hs_deriv μ f hD p c v x hx0).deriv]
  have hg := aux_jhsm_g_strictMonoOn μ f hD (Set.mem_Ioi.mpr hqP) (Set.mem_Ioi.mpr hx0) hx'
  simp only at hg
  have huP := cpp_u_pos μ f hD qP
  have hux := cpp_u_pos μ f hD x
  have hF := cpp_F_lt μ f hD hx' hx0
  -- N(x)/u(x) ≤ N(qP)/u(qP)
  have h1 : ((p - v) * (1 - cdf μ x) - (c - v)) / (1 - cdf μ x) ≤
      ((p - v) * (1 - cdf μ qP) - (c - v)) / (1 - cdf μ qP) := by
    rw [div_le_div_iff₀ hux huP]
    nlinarith [mul_lt_mul_of_pos_left hF hcv]
  have h2 : ((p - v) * (1 - cdf μ qP) - (c - v)) / (1 - cdf μ qP) <
      (p - v) * (qP * f qP / (1 - cdf μ qP)) := by
    rw [div_lt_iff₀ huP]
    have : (p - v) * (qP * f qP / (1 - cdf μ qP)) * (1 - cdf μ qP) = (p - v) * f qP * qP := by
      field_simp
    rw [this]; exact h0
  have h3 := mul_lt_mul_of_pos_left hg hpv
  have h4 : ((p - v) * (1 - cdf μ x) - (c - v)) / (1 - cdf μ x) < (p - v) * (x * f x / (1 - cdf μ x)) := by
    linarith
  rw [div_lt_iff₀ hux] at h4
  have : (p - v) * (x * f x / (1 - cdf μ x)) * (1 - cdf μ x) = (p - v) * f x * x := by
    field_simp
  linarith


lemma cpp_pr_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) : pullRetailerProfit μ p c v 0 = 0 := by
  rw [cpp_pr_eq μ f hD, cpp_S_zero]; simp

lemma cpp_hs_zero (μ : Measure ℝ) (p c v : ℝ) : pushSupplierProfit μ p c v 0 = 0 := by
  rw [cpp_hs_eq]; simp

lemma cpp_pr_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (q : ℝ) (hq : 0 < q)
    (hN : 0 < (p - c) - (p - v) * cdf μ q) : 0 < pullRetailerProfit μ p c v q := by
  rw [cpp_pr_eq μ f hD]
  have := cpp_S_pos μ f hD hq
  have := cpp_u_pos μ f hD q
  positivity

lemma cpp_N_of_pr_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (q : ℝ) (hq : 0 ≤ q)
    (h : 0 < pullRetailerProfit μ p c v q) : 0 < (p - c) - (p - v) * cdf μ q := by
  rw [cpp_pr_eq μ f hD] at h
  have hu := cpp_u_pos μ f hD q
  have hS : 0 ≤ S μ q := by
    rcases hq.lt_or_eq with h' | h'
    · exact (cpp_S_pos μ f hD h').le
    · rw [← h', cpp_S_zero]
  by_contra hc; push_neg at hc
  have : ((p - c) - (p - v) * cdf μ q) * S μ q / (1 - cdf μ q) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc hS) hu.le
  linarith

lemma cpp_N_of_hs_pos (μ : Measure ℝ) (p c v : ℝ) (q : ℝ) (hq : 0 ≤ q)
    (h : 0 < pushSupplierProfit μ p c v q) : 0 < (p - c) - (p - v) * cdf μ q := by
  rw [cpp_hs_eq] at h
  by_contra hc; push_neg at hc
  have := mul_nonpos_of_nonpos_of_nonneg hc hq
  linarith

lemma cpp_exists_max (g : ℝ → ℝ) (hg : Continuous g) (qo : ℝ) (hqo : 0 ≤ qo) (h0 : g 0 = 0)
    (hneg : ∀ y, qo < y → g y ≤ 0) : ∃ x, 0 ≤ x ∧ IsMaxOn g (Set.Ici 0) x := by
  obtain ⟨x, hx, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := qo)).exists_isMaxOn
    (Set.nonempty_Icc.mpr hqo) hg.continuousOn
  refine ⟨x, hx.1, fun y hy => ?_⟩
  have hy' : (0:ℝ) ≤ y := hy
  rcases le_or_gt y qo with h | h
  · exact hmax ⟨hy', h⟩
  · have h1 := hneg y h
    have h2 : g 0 ≤ g x := hmax ⟨le_rfl, hqo⟩
    show g y ≤ g x
    linarith

lemma cpp_deriv_zero_of_max (g : ℝ → ℝ) (x d : ℝ) (hx : 0 < x) (hmax : IsMaxOn g (Set.Ici 0) x)
    (hd : HasDerivAt g d x) : d = 0 :=
  (hmax.isLocalMax (Ici_mem_nhds hx)).hasDerivAt_eq_zero hd

theorem qP_char_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ∃ qP : ℝ, 0 < qP ∧
      (∀ q : ℝ, 0 < q → (pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q ↔ q = qP)) ∧
      (∀ q : ℝ, 0 < q → (pullSupplierProfit μ c v q = pushSupplierProfit μ p c v q ↔ q = qP)) ∧
      IsMaxOn (fun q : ℝ => pullRetailerProfit μ p c v q - pushSupplierProfit μ p c v q)
        (Set.Ici 0) qP ∧
      (∀ q : ℝ, 0 ≤ q →
        IsMaxOn (fun q : ℝ => pullRetailerProfit μ p c v q - pushSupplierProfit μ p c v q)
          (Set.Ici 0) q → q = qP) ∧
      (∀ qstar : ℝ, 0 ≤ qstar → IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar →
        qstar < qP) := by
  obtain ⟨qo, hqo0, hqo⟩ := cpp_exists_qo μ f hD p c v hvc hcp
  obtain ⟨qP, hqP, hqPo, hψ⟩ := cpp_qP_exists μ f hD p c v hvc hcp qo hqo0 hqo
  have hsign := cpp_Kf_sign μ f hD p c v hvc hcp qP hqP hψ
  have hK0 := (hsign qP hqP).2.1 rfl
  have hpv : 0 < p - v := by linarith
  have hcv : 0 < c - v := by linarith
  -- E = Kf / u
  have hE : ∀ q, 0 < q → (pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q ↔ q = qP) := by
    intro q hq
    have e := cpp_E_eq μ f hD p c v q
    have hu := cpp_u_pos μ f hD q
    constructor
    · intro h
      rw [h, sub_self] at e
      have hk : (p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q = 0 := by
        rcases div_eq_zero_iff.mp e.symm with h' | h'
        · exact h'
        · linarith
      rcases lt_trichotomy q qP with h' | h' | h'
      · linarith [(hsign q hq).1 h']
      · exact h'
      · linarith [(hsign q hq).2.2 h']
    · rintro rfl
      rw [hK0, zero_div] at e
      linarith
  refine ⟨qP, hqP, hE, ?_, ?_⟩
  · intro q hq
    rw [← hE q hq]
    have h1 := cpp_sum_pull μ p c v q
    have h2 := cpp_sum_push μ p c v q
    constructor <;> intro h <;> linarith
  -- D
  set D := fun q : ℝ => pullRetailerProfit μ p c v q - pushSupplierProfit μ p c v q with hDdef
  have hDc : Continuous D := (cpp_pr_cont μ f hD p c v).sub (cpp_hs_cont μ f hD p c v)
  have hDd : ∀ x, 0 < x → HasDerivAt D
      (f x / (1 - cdf μ x) ^ 2 * ((p - v) * (1 - cdf μ x) ^ 2 * x - (c - v) * S μ x)) x := by
    intro x hx
    have h := (cpp_pr_deriv μ f hD p c v x hx).sub (cpp_hs_deriv μ f hD p c v x hx)
    refine h.congr_deriv ?_
    have hu := (cpp_u_pos μ f hD x).ne'
    field_simp
    ring
  have hmono : StrictMonoOn D (Set.Icc 0 qP) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 qP) hDc.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hDd x hx.1).deriv]
    have := (hsign x hx.1).1 hx.2
    have := cpp_f_pos μ f hD x hx.1
    have := cpp_u_pos μ f hD x
    positivity
  have hanti : StrictAntiOn D (Set.Ici qP) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici qP) hDc.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    have hx' : qP < x := hx
    rw [(hDd x (by linarith)).deriv]
    have := (hsign x (by linarith)).2.2 hx'
    have := cpp_f_pos μ f hD x (by linarith)
    have := cpp_u_pos μ f hD x
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  have hmax : IsMaxOn D (Set.Ici 0) qP := by
    intro y hy
    have hy' : (0:ℝ) ≤ y := hy
    show D y ≤ D qP
    rcases le_or_gt y qP with h | h
    · exact hmono.monotoneOn ⟨hy', h⟩ ⟨hqP.le, le_rfl⟩ h
    · exact (hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h).le
  refine ⟨hmax, ?_, ?_⟩
  · intro q hq hqmax
    have h1 : D qP ≤ D q := hqmax (Set.mem_Ici.mpr hqP.le)
    rcases lt_trichotomy q qP with h | h | h
    · have := hmono ⟨hq, h.le⟩ ⟨hqP.le, le_rfl⟩ h
      linarith
    · exact h
    · have := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr h.le) h
      linarith
  · intro qstar hqs hmaxs
    have hpos : 0 < pullRetailerProfit μ p c v qP :=
      cpp_pr_pos μ f hD p c v qP hqP (cpp_N_pos μ f hD p c v hvc hcp qo hqo0 hqo qP hqPo)
    have hqs0 : 0 < qstar := by
      rcases hqs.lt_or_eq with h | h
      · exact h
      · have : pullRetailerProfit μ p c v qP ≤ pullRetailerProfit μ p c v qstar :=
          hmaxs (Set.mem_Ici.mpr hqP.le)
        rw [← h, cpp_pr_zero μ f hD] at this
        linarith
    have hd0 := cpp_deriv_zero_of_max _ _ _ hqs0 hmaxs (cpp_pr_deriv μ f hD p c v qstar hqs0)
    by_contra hcon; push_neg at hcon
    have hneg := cpp_prd_neg_qP μ f hD p c v hvc hcp qP hqP hK0
    rcases hcon.lt_or_eq with h | h
    · have := cpp_prd_anti μ f hD p c v hvc hcp hqP h
      linarith
    · rw [← h] at hd0; linarith

theorem pull_beats_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    (∃ qstar : ℝ, 0 ≤ qstar ∧ IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar) ∧
    (∃ qhat : ℝ, 0 ≤ qhat ∧ IsMaxOn (pushSupplierProfit μ p c v) (Set.Ici 0) qhat) ∧
    ∀ qstar qhat : ℝ, 0 ≤ qstar → IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar →
      0 ≤ qhat → IsMaxOn (pushSupplierProfit μ p c v) (Set.Ici 0) qhat →
      pushSupplierProfit μ p c v qhat < pullRetailerProfit μ p c v qstar ∧
      qhat < qstar ∧
      chainProfit μ p c v qhat < chainProfit μ p c v qstar := by
  obtain ⟨qo, hqo0, hqo⟩ := cpp_exists_qo μ f hD p c v hvc hcp
  have hpv : 0 < p - v := by linarith
  have hcv : 0 < c - v := by linarith
  have e : (p - v) * cdf μ qo = p - c := by rw [hqo]; field_simp
  have hNneg : ∀ y, qo < y → (p - c) - (p - v) * cdf μ y < 0 := by
    intro y hy
    have := cpp_F_lt μ f hD hy (by linarith)
    nlinarith
  refine ⟨cpp_exists_max _ (cpp_pr_cont μ f hD p c v) qo hqo0.le (cpp_pr_zero μ f hD p c v) ?_,
    cpp_exists_max _ (cpp_hs_cont μ f hD p c v) qo hqo0.le (cpp_hs_zero μ p c v) ?_, ?_⟩
  · intro y hy
    rw [cpp_pr_eq μ f hD]
    have := hNneg y hy
    have := cpp_S_pos μ f hD (show 0 < y by linarith)
    have := cpp_u_pos μ f hD y
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
      (by linarith)
  · intro y hy
    rw [cpp_hs_eq]
    have := hNneg y hy
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  intro qstar qhat hqs hmaxs hqh hmaxh
  have hm := (show 0 < qo / 2 by linarith)
  have hNm := cpp_N_pos μ f hD p c v hvc hcp qo hqo0 hqo (qo / 2) (by linarith)
  have hprm : 0 < pullRetailerProfit μ p c v (qo / 2) := cpp_pr_pos μ f hD p c v _ hm hNm
  have hhsm : 0 < pushSupplierProfit μ p c v (qo / 2) := by
    rw [cpp_hs_eq]; positivity
  have hprs : 0 < pullRetailerProfit μ p c v qstar := lt_of_lt_of_le hprm (hmaxs (Set.mem_Ici.mpr hm.le))
  have hhsh : 0 < pushSupplierProfit μ p c v qhat := lt_of_lt_of_le hhsm (hmaxh (Set.mem_Ici.mpr hm.le))
  have hqs0 : 0 < qstar := by
    rcases hqs.lt_or_eq with h | h
    · exact h
    · rw [← h, cpp_pr_zero μ f hD] at hprs; linarith
  have hqh0 : 0 < qhat := by
    rcases hqh.lt_or_eq with h | h
    · exact h
    · rw [← h, cpp_hs_zero] at hhsh; linarith
  have hNs := cpp_N_of_pr_pos μ f hD p c v qstar hqs hprs
  have hNh := cpp_N_of_hs_pos μ p c v qhat hqh hhsh
  have hqso := cpp_lt_qo μ f hD p c v hvc hcp qo hqo qstar hNs
  have hqho := cpp_lt_qo μ f hD p c v hvc hcp qo hqo qhat hNh
  have hds := cpp_deriv_zero_of_max _ _ _ hqs0 hmaxs (cpp_pr_deriv μ f hD p c v qstar hqs0)
  have hdh := cpp_deriv_zero_of_max _ _ _ hqh0 hmaxh (cpp_hs_deriv μ f hD p c v qhat hqh0)
  -- π_r'(qhat) > 0
  have hpos : 0 < (p - v) * (1 - cdf μ qhat) - (c - v) -
      (c - v) * (S μ qhat * f qhat / (1 - cdf μ qhat) ^ 2) := by
    have hA := cpp_factA μ f hD qhat hqh0
    have hf := cpp_f_pos μ f hD qhat hqh0
    have hu := cpp_u_pos μ f hD qhat
    have hS := cpp_S_pos μ f hD hqh0
    set u := 1 - cdf μ qhat
    have ecv : c - v = (p - v) * (u - f qhat * qhat) := by linarith
    have key : ((p - v) * u - (c - v) - (c - v) * (S μ qhat * f qhat / u ^ 2)) * u ^ 2 =
        (p - v) * f qhat * (qhat * u ^ 2 - u * S μ qhat + f qhat * qhat * S μ qhat) := by
      rw [ecv]
      field_simp
      ring
    have : 0 < ((p - v) * u - (c - v) - (c - v) * (S μ qhat * f qhat / u ^ 2)) * u ^ 2 := by
      rw [key]
      apply mul_pos (mul_pos hpv hf)
      linarith
    exact pos_of_mul_pos_left this (by positivity)
  have hlt : qhat < qstar := by
    by_contra hc; push_neg at hc
    rcases hc.lt_or_eq with h | h
    · have := cpp_prd_anti μ f hD p c v hvc hcp hqs0 h
      linarith
    · rw [h] at hds; linarith
  refine ⟨?_, hlt, ?_⟩
  · have h1 : pushSupplierProfit μ p c v qhat < pullRetailerProfit μ p c v qhat := by
      rw [cpp_hs_eq, cpp_pr_eq μ f hD]
      have hu := cpp_u_pos μ f hD qhat
      have hSg := cpp_S_gt μ f hD hqh0
      rw [lt_div_iff₀ hu]
      nlinarith [mul_lt_mul_of_pos_left hSg hNh]
    exact lt_of_lt_of_le h1 (hmaxs (Set.mem_Ici.mpr hqh))
  · exact cpp_chain_smono μ f hD p c v hvc hcp qo hqo0 hqo ⟨hqh, hqho.le⟩ ⟨hqs, hqso.le⟩ hlt


lemma cpp_E_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qP : ℝ) (hqP : 0 < qP) (hψ : (p - v) * cppPsi μ qP = c - v) (q : ℝ) (hq : 0 < q) :
    pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q ↔ q = qP := by
  have hsign := cpp_Kf_sign μ f hD p c v hvc hcp qP hqP hψ
  have hK0 := (hsign qP hqP).2.1 rfl
  have e := cpp_E_eq μ f hD p c v q
  have hu := cpp_u_pos μ f hD q
  constructor
  · intro h
    rw [h, sub_self] at e
    have hk : (p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q = 0 := by
      rcases div_eq_zero_iff.mp e.symm with h' | h'
      · exact h'
      · linarith
    rcases lt_trichotomy q qP with h' | h' | h'
    · linarith [(hsign q hq).1 h']
    · exact h'
    · linarith [(hsign q hq).2.2 h']
  · rintro rfl
    rw [hK0, zero_div] at e
    linarith

lemma cpp_adm_iff (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo0 : 0 < qo) (hqo : cdf μ qo = (p - c) / (p - v)) (k : Contract) :
    k.IsAdmissible μ p c v ↔ 0 ≤ k.q ∧ k.q ≤ qo := by
  have hpv : 0 < p - v := by linarith
  have e : (p - v) * cdf μ qo = p - c := by rw [hqo]; field_simp
  have hN : ∀ q, 0 ≤ (p - c) - (p - v) * cdf μ q ↔ q ≤ qo := by
    intro q
    constructor
    · exact cpp_le_qo μ f hD p c v hvc hcp qo hqo0 hqo q
    · intro h
      have := (cdf μ).mono h
      nlinarith
  obtain ⟨m, q⟩ := k
  have hF0 := cdf_nonneg μ q
  have hu := cpp_u_pos μ f hD q
  cases m with
  | push =>
    simp only [Contract.IsAdmissible, Contract.wholesalePrice, pushPrice]
    rw [← hN q]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith, by nlinarith⟩
  | pull =>
    simp only [Contract.IsAdmissible, Contract.wholesalePrice, pullPrice]
    rw [← hN q, le_div_iff₀ hu, div_le_iff₀ hu]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith, by linarith⟩

lemma cpp_payoff_sum (μ : Measure ℝ) (p c v : ℝ) (k : Contract) :
    k.retailerPayoff μ p c v + k.supplierPayoff μ p c v = chainProfit μ p c v k.q := by
  obtain ⟨m, q⟩ := k
  cases m with
  | push => exact cpp_sum_push μ p c v q
  | pull => exact cpp_sum_pull μ p c v q

theorem pareto_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    ∃ qP : ℝ, 0 < qP ∧ qP < qo ∧
      pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP ∧
      pullSupplierProfit μ c v qP = pushSupplierProfit μ p c v qP ∧
      (∀ q : ℝ, 0 < q → pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q → q = qP) ∧
      paretoSet μ p c v = {k : Contract | k.q ∈ Set.Icc qP qo} ∧
      ∀ q ∈ Set.Icc qP qo, SurvivesPushChallenge μ p c v q := by
  have hpv : 0 < p - v := by linarith
  have hcv : 0 < c - v := by linarith
  have e : (p - v) * cdf μ qo = p - c := by rw [hqo]; field_simp
  have hqo0 : 0 < qo := by
    by_contra h; push_neg at h
    rw [cpp_F_zero μ f hD qo h] at e
    linarith
  obtain ⟨qP, hqP, hqPo, hψ⟩ := cpp_qP_exists μ f hD p c v hvc hcp qo hqo0 hqo
  have hsign := cpp_Kf_sign μ f hD p c v hvc hcp qP hqP hψ
  have hK0 := (hsign qP hqP).2.1 rfl
  have hEq : pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP :=
    (cpp_E_iff μ f hD p c v hvc hcp qP hqP hψ qP hqP).mpr rfl
  have hsum1 := cpp_sum_pull μ p c v
  have hsum2 := cpp_sum_push μ p c v
  have hEs : pullSupplierProfit μ c v qP = pushSupplierProfit μ p c v qP := by
    linarith [hsum1 qP, hsum2 qP]
  have hchain := cpp_chain_smono μ f hD p c v hvc hcp qo hqo0 hqo
  have hadm := cpp_adm_iff μ f hD p c v hvc hcp qo hqo0 hqo
  have hNo : (p - c) - (p - v) * cdf μ qo = 0 := by linarith
  have hpr_qo : pullRetailerProfit μ p c v qo = 0 := by rw [cpp_pr_eq μ f hD, hNo]; simp
  have hhs_qo : pushSupplierProfit μ p c v qo = 0 := by rw [cpp_hs_eq, hNo]; simp
  have hchain0 : chainProfit μ p c v 0 = 0 := by simp [chainProfit, cpp_S_zero]
  have hchain_lt : ∀ q, 0 ≤ q → q < qo → chainProfit μ p c v q < chainProfit μ p c v qo :=
    fun q h1 h2 => hchain ⟨h1, h2.le⟩ ⟨hqo0.le, le_rfl⟩ h2
  -- E sign on [qP, ∞)
  have hKle : ∀ q, qP ≤ q → pullRetailerProfit μ p c v q ≤ pushRetailerProfit μ p v q := by
    intro q hq
    have hq0 : 0 < q := by linarith
    have e2 := cpp_E_eq μ f hD p c v q
    have hu := cpp_u_pos μ f hD q
    have hk : (p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q ≤ 0 := by
      rcases hq.lt_or_eq with h | h
      · exact ((hsign q hq0).2.2 h).le
      · exact ((hsign q hq0).2.1 h.symm).le
    have : ((p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q) / (1 - cdf μ q) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hk hu.le
    linarith
  have hKgt : ∀ q, 0 < q → q < qP → pushRetailerProfit μ p v q < pullRetailerProfit μ p c v q := by
    intro q hq0 hq
    have e2 := cpp_E_eq μ f hD p c v q
    have hu := cpp_u_pos μ f hD q
    have hk := (hsign q hq0).1 hq
    have : 0 < ((p - v) * (1 - cdf μ q) ^ 2 * q - (c - v) * S μ q) / (1 - cdf μ q) :=
      div_pos hk hu
    linarith
  have hpranti := cpp_pr_anti_after μ f hD p c v hvc hcp qP hqP hK0
  have hhsanti := cpp_hs_anti_after μ f hD p c v hvc hcp qP hqP hK0
  refine ⟨qP, hqP, hqPo, hEq, hEs, fun q hq h => (cpp_E_iff μ f hD p c v hvc hcp qP hqP hψ q hq).mp h,
    ?_, fun q hq => (pull_survives_core μ f hD p c v hvc hcp qP hqP hEq q hq.1).2.2⟩
  ext k
  simp only [paretoSet, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨hk, hnd⟩
    have hk' := (hadm k).mp hk
    refine ⟨?_, hk'.2⟩
    by_contra hlt; push_neg at hlt
    apply hnd
    obtain ⟨m, q⟩ := k
    simp only at hk' hlt
    rcases hk'.1.lt_or_eq with hq0 | hq0
    · -- 0 < q < qP
      have hE := hKgt q hq0 hlt
      have hqqo : q < qo := by linarith
      cases m with
      | pull =>
        have hps0 : 0 ≤ pullSupplierProfit μ c v q := by
          rw [cpp_ps_eq μ f hD]
          have := cpp_S_gt μ f hD hq0
          have hu := cpp_u_pos μ f hD q
          have : q ≤ S μ q / (1 - cdf μ q) := by rw [le_div_iff₀ hu]; linarith
          nlinarith
        have hhr_qo : pushRetailerProfit μ p v qo = chainProfit μ p c v qo := by
          linarith [hsum2 qo]
        obtain ⟨r, hr, hrv⟩ := intermediate_value_Icc hqqo.le (cpp_hr_cont μ f hD p v).continuousOn
          (show pullRetailerProfit μ p c v q ∈ Set.Icc (pushRetailerProfit μ p v q)
            (pushRetailerProfit μ p v qo) from ⟨hE.le, by
              rw [hhr_qo]; linarith [hsum1 q, hchain_lt q hq0.le hqqo]⟩)
        have hrq : q < r := by
          rcases hr.1.lt_or_eq with h | h
          · exact h
          · rw [← h] at hrv; linarith
        have hch := hchain ⟨hq0.le, hqqo.le⟩ ⟨by linarith, hr.2⟩ hrq
        refine ⟨⟨Mode.push, r⟩, (hadm _).mpr ⟨by simp; linarith, hr.2⟩, ?_⟩
        simp only [Contract.ParetoDominates, Contract.retailerPayoff, Contract.supplierPayoff]
        have := hsum2 r
        have := hsum1 q
        refine ⟨by rw [hrv], by linarith, Or.inr (by linarith)⟩
      | push =>
        have hhr0 : 0 ≤ pushRetailerProfit μ p v q := by
          rw [cpp_hr_eq]
          have := cpp_S_gt μ f hD hq0
          nlinarith
        have hps_qo : pullSupplierProfit μ c v qo = chainProfit μ p c v qo := by
          linarith [hsum1 qo]
        have hEs' : pullSupplierProfit μ c v q < pushSupplierProfit μ p c v q := by
          linarith [hsum1 q, hsum2 q]
        obtain ⟨r, hr, hrv⟩ := intermediate_value_Icc hqqo.le (cpp_ps_cont μ f hD c v).continuousOn
          (show pushSupplierProfit μ p c v q ∈ Set.Icc (pullSupplierProfit μ c v q)
            (pullSupplierProfit μ c v qo) from ⟨hEs'.le, by
              rw [hps_qo]; linarith [hsum2 q, hchain_lt q hq0.le hqqo]⟩)
        have hrq : q < r := by
          rcases hr.1.lt_or_eq with h | h
          · exact h
          · rw [← h] at hrv; linarith
        have hch := hchain ⟨hq0.le, hqqo.le⟩ ⟨by linarith, hr.2⟩ hrq
        refine ⟨⟨Mode.pull, r⟩, (hadm _).mpr ⟨by simp; linarith, hr.2⟩, ?_⟩
        simp only [Contract.ParetoDominates, Contract.retailerPayoff, Contract.supplierPayoff]
        have := hsum1 r
        have := hsum2 q
        refine ⟨by linarith, by rw [hrv], Or.inl (by linarith)⟩
    · -- q = 0
      subst hq0
      have hz1 : pullSupplierProfit μ c v 0 = 0 := by rw [cpp_ps_eq μ f hD, cpp_S_zero]; simp
      have hz2 : pushRetailerProfit μ p v 0 = 0 := by rw [cpp_hr_eq, cpp_S_zero]; simp
      have hz3 := cpp_pr_zero μ f hD p c v
      have hz4 := cpp_hs_zero μ p c v
      have hpos : 0 < pullSupplierProfit μ c v qo := by
        have := hchain_lt 0 le_rfl hqo0
        linarith [hsum1 qo]
      refine ⟨⟨Mode.pull, qo⟩, (hadm _).mpr ⟨hqo0.le, le_rfl⟩, ?_⟩
      cases m <;>
        simp only [Contract.ParetoDominates, Contract.retailerPayoff, Contract.supplierPayoff] <;>
        simp only [hz1, hz2, hz3, hz4, hpr_qo] <;>
        exact ⟨le_rfl, hpos.le, Or.inr hpos⟩
  · rintro ⟨h1, h2⟩
    refine ⟨(hadm k).mpr ⟨by linarith, h2⟩, ?_⟩
    rintro ⟨k', hk', hdom⟩
    have hk'' := (hadm k').mp hk'
    have hs := cpp_payoff_sum μ p c v k
    have hs' := cpp_payoff_sum μ p c v k'
    obtain ⟨hd1, hd2, hd3⟩ := hdom
    have hch : chainProfit μ p c v k.q < chainProfit μ p c v k'.q := by
      rcases hd3 with h | h <;> linarith
    have hlt : k.q < k'.q := by
      by_contra hc; push_neg at hc
      have := hchain.monotoneOn ⟨hk''.1, hk''.2⟩ ⟨by linarith, h2⟩ hc
      linarith
    obtain ⟨m, q⟩ := k
    obtain ⟨m', r⟩ := k'
    simp only at h1 h2 hlt hd1 hd2
    have hq := hKle q h1
    have hPq : pushSupplierProfit μ p c v q ≤ pullSupplierProfit μ c v q := by
      linarith [hsum1 q, hsum2 q]
    have hA := hpranti (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (by linarith)) hlt
    have hB := hhsanti (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (by linarith)) hlt
    cases m <;> cases m' <;>
      simp only [Contract.retailerPayoff, Contract.supplierPayoff] at hd1 hd2 <;> linarith

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    ∃ qP : ℝ, 0 < qP ∧ qP < qo ∧
      pullRetailerProfit μ p c v qP = pushRetailerProfit μ p v qP ∧
      pullSupplierProfit μ c v qP = pushSupplierProfit μ p c v qP ∧
      (∀ q : ℝ, 0 < q → pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q → q = qP) ∧
      paretoSet μ p c v = {k : Contract | k.q ∈ Set.Icc qP qo} ∧
      ∀ q ∈ Set.Icc qP qo, SurvivesPushChallenge μ p c v q := by
  exact pareto_core μ f hD p c v hvc hcp qo hqo
