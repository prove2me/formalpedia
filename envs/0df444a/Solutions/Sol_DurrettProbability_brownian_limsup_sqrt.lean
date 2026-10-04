-- Prove2me | solution 1 for DurrettProbability.brownian_limsup_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:44:25.170586+00:00
-- url     : https://prove2.me/submissions/6839d1d8-2d02-4503-9e3c-fe644c8b93a8

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology ENNReal

namespace P2M09f66952

noncomputable def tm (k : ℕ) : ℝ≥0 := 2 ^ (k * k)

lemma tm_coe (k : ℕ) : ((tm k : ℝ≥0) : ℝ) = (2 : ℝ) ^ (k * k) := by
  simp [tm]

lemma tm_pos (k : ℕ) : (0 : ℝ) < tm k := by
  rw [tm_coe]; positivity

lemma tm_succ (k : ℕ) : ((tm (k + 1) : ℝ≥0) : ℝ) = (tm k : ℝ) * 2 ^ (2 * k + 1) := by
  rw [tm_coe, tm_coe, ← pow_add]; congr 1; ring

lemma tm_mono : Monotone tm := by
  apply monotone_nat_of_le_succ
  intro k
  rw [← NNReal.coe_le_coe, tm_succ]
  have h1 := tm_pos k
  have h2 : (1 : ℝ) ≤ 2 ^ (2 * k + 1) := one_le_pow₀ (by norm_num)
  nlinarith

lemma tm_ratio (k : ℕ) : (tm k : ℝ) / tm (k + 1) ≤ (2⁻¹ : ℝ) ^ k := by
  have hp := tm_pos k
  rw [tm_succ, div_le_iff₀ (by positivity)]
  have h1 : (2⁻¹ : ℝ) ^ k * 2 ^ (2 * k + 1) = 2 ^ (k + 1) := by
    rw [show 2 * k + 1 = k + (k + 1) by ring, pow_add, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ (by norm_num), one_pow, one_mul]
  have h2 : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
  calc (tm k : ℝ) ≤ tm k * 2 ^ (k + 1) := le_mul_of_one_le_right hp.le h2
    _ = (2⁻¹ : ℝ) ^ k * (tm k * 2 ^ (2 * k + 1)) := by rw [← h1]; ring

lemma tm_three (k : ℕ) : 4 * (tm k : ℝ) ≤ 3 * tm (k + 1) := by
  rw [tm_succ]
  have hp := tm_pos k
  have h2 : (2 : ℝ) ^ 1 ≤ 2 ^ (2 * k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

lemma tm_tendsto : Tendsto tm atTop atTop := by
  refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
  have h : k ≤ 2 ^ (k * k) :=
    (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self k))
  rw [← NNReal.coe_le_coe, tm_coe]
  exact_mod_cast h

lemma gauss_tail_pos (c : ℝ) : 0 < gaussianReal 0 1 (Set.Ioi c) := by
  rw [pos_iff_ne_zero]
  intro h
  have := gaussianReal_absolutelyContinuous' 0 (one_ne_zero) h
  simp at this

lemma gauss_tail_mono {v : ℝ≥0} (hv : 0 < (v : ℝ)) {a c : ℝ} (h : a ≤ c * Real.sqrt v) :
    gaussianReal 0 1 (Set.Ioi c) ≤ gaussianReal 0 v (Set.Ioi a) := by
  have hmap : (gaussianReal 0 1).map (Real.sqrt v * ·) = gaussianReal 0 v := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp
  rw [← hmap, Measure.map_apply (measurable_const_mul _) measurableSet_Ioi]
  apply measure_mono
  intro x hx
  simp only [Set.mem_preimage, Set.mem_Ioi] at hx ⊢
  have hs := Real.sqrt_pos.2 hv
  rw [mul_comm]
  exact h.trans_lt (mul_lt_mul_of_pos_right hx hs)

theorem upper {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ K : ℝ, ∃ᶠ t : ℝ≥0 in atTop, K < B t ω / Real.sqrt t := by
  set C : ℝ≥0 → Ω → ℝ := fun t => (hB.aemeasurable t).mk (B t) with hCdef
  have hCm : ∀ t, Measurable (C t) := fun t => (hB.aemeasurable t).measurable_mk
  have hC : IsPreBrownianReal C P := hB.congr (fun t => (hB.aemeasurable t).ae_eq_mk)
  have hBC : ∀ᵐ ω ∂P, ∀ k, B (tm k) ω = C (tm k) ω :=
    ae_all_iff.2 (fun k => (hB.aemeasurable (tm k)).ae_eq_mk)
  have key : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ᶠ k in atTop,
      ((j : ℝ) + 1) * Real.sqrt (tm (k + 1)) < C (tm (k + 1)) ω := by
    intro j
    set K : ℝ := (j : ℝ) + 1 with hK
    have hK1 : 1 ≤ K := by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hK0 : 0 < K := by linarith
    let A : ℕ → Set Ω := fun k =>
      {ω | 2 * K * Real.sqrt (tm (k + 1)) < C (tm (k + 1)) ω - C (tm k) ω}
    have hAm : ∀ k, MeasurableSet (A k) := fun k =>
      measurableSet_lt measurable_const ((hCm _).sub (hCm _))
    have hAind : iIndepSet A P := by
      rw [iIndepSet_iff_meas_biInter hAm]
      intro s
      exact (hC.hasIndepIncrements.nat (t := tm) tm_mono).measure_inter_preimage_eq_mul s
        (sets := fun k => Set.Ioi (2 * K * Real.sqrt (tm (k + 1))))
        (fun _ _ => measurableSet_Ioi)
    have hAlow : ∀ k, gaussianReal 0 1 (Set.Ioi (4 * K)) ≤ P (A k) := by
      intro k
      have hlaw := hC.hasLaw_sub (tm (k + 1)) (tm k)
      have hmono : (tm k : ℝ) ≤ tm (k + 1) := NNReal.coe_le_coe.2 (tm_mono (Nat.le_succ k))
      have h3 := tm_three k
      have hpk := tm_pos k
      have hv : ((nndist (tm (k + 1)).1 (tm k).1 : ℝ≥0) : ℝ) = (tm (k + 1) : ℝ) - tm k := by
        rw [coe_nndist, Real.dist_eq, abs_of_nonneg]
        · rfl
        · simp only [NNReal.val_eq_coe]; linarith
      have hP : P (A k) =
          gaussianReal 0 (nndist (tm (k + 1)).1 (tm k).1)
            (Set.Ioi (2 * K * Real.sqrt (tm (k + 1)))) := by
        rw [← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable measurableSet_Ioi]
        rfl
      rw [hP]
      apply gauss_tail_mono
      · rw [hv]; linarith
      · rw [hv]
        have hsq : Real.sqrt (tm (k + 1)) ≤ 2 * Real.sqrt ((tm (k + 1) : ℝ) - tm k) := by
          rw [show (2 : ℝ) = Real.sqrt 4 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
            ← Real.sqrt_mul (by norm_num)]
          exact Real.sqrt_le_sqrt (by linarith)
        have := mul_le_mul_of_nonneg_left hsq (by linarith : (0 : ℝ) ≤ 2 * K)
        linarith
    have hsumA : ∑' k, P (A k) = ∞ := by
      refine top_unique ?_
      calc (∞ : ℝ≥0∞) = ∑' _k : ℕ, gaussianReal 0 1 (Set.Ioi (4 * K)) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (gauss_tail_pos _).ne').symm
        _ ≤ ∑' k, P (A k) := ENNReal.tsum_le_tsum hAlow
    have hlimA : P (limsup A atTop) = 1 := measure_limsup_eq_one hAm hAind hsumA
    have haeA : ∀ᵐ ω ∂P, ∃ᶠ k in atTop, ω ∈ A k := by
      have hms : MeasurableSet (limsup A atTop) := MeasurableSet.measurableSet_limsup hAm
      have h0 : P (limsup A atTop)ᶜ = 0 := (prob_compl_eq_zero_iff hms).2 hlimA
      rw [ae_iff]
      convert h0 using 2
      ext ω
      simp [Filter.mem_limsup_iff_frequently_mem]
    let D : ℕ → Set Ω := fun k => {ω | K * Real.sqrt (tm (k + 1)) ≤ |C (tm k) ω|}
    have hDle : ∀ k, P (D k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
      intro k
      have hc : 0 < K * Real.sqrt (tm (k + 1)) := mul_pos hK0 (Real.sqrt_pos.2 (tm_pos _))
      have hcheb := meas_ge_le_variance_div_sq
        (hC.isGaussianProcess.hasGaussianLaw_eval (tm k)).memLp_two hc
      rw [hC.integral_eval, (hC.hasLaw_eval _).variance_eq, variance_id_gaussianReal] at hcheb
      simp only [sub_zero] at hcheb
      refine hcheb.trans ?_
      rw [show ((2⁻¹ : ℝ≥0∞)) ^ k = ENNReal.ofReal ((2⁻¹ : ℝ) ^ k) by
        rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
          ENNReal.ofReal_ofNat]]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_pow, Real.sq_sqrt (tm_pos _).le]
      have hK2 : 1 ≤ K ^ 2 := by nlinarith
      have hq := tm_pos (k + 1)
      calc (tm k : ℝ) / (K ^ 2 * tm (k + 1)) ≤ tm k / tm (k + 1) := by
            apply div_le_div_of_nonneg_left (tm_pos k).le hq
            nlinarith
        _ ≤ _ := tm_ratio k
    have hsumD : ∑' k, P (D k) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hDle)
      rw [ENNReal.tsum_geometric]
      simp
    have haeD := ae_eventually_notMem hsumD
    filter_upwards [haeA, haeD] with ω h1 h2
    refine (h1.and_eventually h2).mono fun k hk => ?_
    have hk1 : 2 * K * Real.sqrt (tm (k + 1)) < C (tm (k + 1)) ω - C (tm k) ω := hk.1
    have hk2 : ¬ (K * Real.sqrt (tm (k + 1)) ≤ |C (tm k) ω|) := hk.2
    rw [not_le] at hk2
    have := neg_abs_le (C (tm k) ω)
    linarith
  filter_upwards [ae_all_iff.2 key, hBC] with ω hkey hB' K
  obtain ⟨j, hj⟩ := exists_nat_gt K
  have htend : Tendsto (fun k => tm (k + 1)) atTop atTop :=
    tm_tendsto.comp (tendsto_add_atTop_nat 1)
  refine htend.frequently ((hkey j).mono fun k hk => ?_)
  have hs := Real.sqrt_pos.2 (tm_pos (k + 1))
  rw [hB' (k + 1), lt_div_iff₀ hs]
  have : K * Real.sqrt (tm (k + 1)) < ((j : ℝ) + 1) * Real.sqrt (tm (k + 1)) :=
    mul_lt_mul_of_pos_right (by linarith) hs
  linarith

end P2M09f66952

open Filter MeasureTheory ProbabilityTheory DurrettProbability in open scoped NNReal Topology in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, (∀ K : ℝ, ∃ᶠ t : ℝ≥0 in atTop, K < B t ω / Real.sqrt t)
      ∧ (∀ K : ℝ, ∃ᶠ t : ℝ≥0 in atTop, B t ω / Real.sqrt t < K) := by
  filter_upwards [P2M09f66952.upper hB.toIsPreBrownianReal,
    P2M09f66952.upper hB.toIsPreBrownianReal.neg] with ω h1 h2
  refine ⟨h1, fun K => (h2 (-K)).mono fun t ht => ?_⟩
  simp only [Pi.neg_apply, neg_div] at ht
  linarith
