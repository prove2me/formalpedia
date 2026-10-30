-- Prove2me | solution 1 for DistFreePricing.Maximin.theorem_1_b_tight
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:34:33.920308+00:00
-- url     : https://prove2.me/submissions/c24d3ae7-6653-4f60-961f-49e2f7660971

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting
import Theorems.Thm_DistFreePricing_Maximin_kStar_le
import Theorems.Thm_DistFreePricing_Maximin_eq_OA_4_cardano
import Theorems.Thm_DistFreePricing_Maximin_eq_OA_5

open MeasureTheory DistFreePricing.Maximin Filter Topology

lemma dfp_twoPoint_int (μ σ k : ℝ) (f : ℝ → ℝ) :
    Integrable f (twoPoint μ σ k) := by
  unfold twoPoint
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma dfp_twoPoint_integral (μ σ k : ℝ) (f : ℝ → ℝ) (hk : 0 < k) :
    ∫ v, f v ∂(twoPoint μ σ k) =
      1 / (1 + k ^ 2) * f (μ - k * σ) + (1 - 1 / (1 + k ^ 2)) * f (μ + σ / k) := by
  have hw1 : 0 ≤ 1 / (1 + k ^ 2) := by positivity
  have hw2 : 0 ≤ 1 - 1 / (1 + k ^ 2) := by
    rw [sub_nonneg]; apply div_le_one_of_le₀ (by nlinarith) (by positivity)
  unfold twoPoint
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac, ENNReal.toReal_ofReal hw1, ENNReal.toReal_ofReal hw2, smul_eq_mul, smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

lemma dfp_twoPoint_real (μ σ k : ℝ) (hk : 0 < k) (S : Set ℝ) (hS : MeasurableSet S) :
    ((twoPoint μ σ k) S).toReal =
      1 / (1 + k ^ 2) * S.indicator 1 (μ - k * σ) +
        (1 - 1 / (1 + k ^ 2)) * S.indicator 1 (μ + σ / k) := by
  have h := dfp_twoPoint_integral μ σ k (S.indicator 1) hk
  rw [integral_indicator_one hS] at h
  exact h

lemma dfp_twoPoint_mem (μ σ k : ℝ) (hσ : 0 < σ) (hk : 0 < k) (hkμ : k * σ ≤ μ) :
    twoPoint μ σ k ∈ valClass μ σ := by
  have hw1 : 0 ≤ 1 / (1 + k ^ 2) := by positivity
  have hw2 : 0 ≤ 1 - 1 / (1 + k ^ 2) := by
    rw [sub_nonneg]; apply div_le_one_of_le₀ (by nlinarith) (by positivity)
  have hb : 0 < μ + σ / k := by
    have : 0 < σ / k := div_pos hσ hk
    have : 0 < k * σ := mul_pos hk hσ
    linarith
  have h1k : (1 + k ^ 2) ≠ 0 := by positivity
  refine ⟨?_, ?_, dfp_twoPoint_int _ _ _ _, dfp_twoPoint_int _ _ _ _, ?_, ?_⟩
  · constructor
    unfold twoPoint
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hw1 hw2]; simp
  · unfold twoPoint
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ measurableSet_Iio, Measure.dirac_apply' _ measurableSet_Iio]
    rw [Set.indicator_of_notMem (by simp; linarith), Set.indicator_of_notMem (by simp; linarith)]
    simp
  · rw [dfp_twoPoint_integral _ _ _ _ hk]
    field_simp; ring
  · rw [dfp_twoPoint_integral _ _ _ _ hk]
    field_simp; ring

lemma dfp_twoPoint_Ici_le (μ σ k p : ℝ) (hk : 0 < k) (hp : μ - k * σ < p) :
    ((twoPoint μ σ k) (Set.Ici p)).toReal ≤ 1 - 1 / (1 + k ^ 2) := by
  have hw2 : 0 ≤ 1 - 1 / (1 + k ^ 2) := by
    rw [sub_nonneg]; apply div_le_one_of_le₀ (by nlinarith) (by positivity)
  rw [dfp_twoPoint_real _ _ _ hk _ measurableSet_Ici,
    Set.indicator_of_notMem (by simp; linarith)]
  have : Set.indicator (Set.Ici p) (1 : ℝ → ℝ) (μ + σ / k) ≤ 1 := by
    by_cases h : μ + σ / k ∈ Set.Ici p
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; norm_num
  nlinarith

lemma dfp_twoPoint_Ici_eq (μ σ k p : ℝ) (hk : 0 < k) (hp : μ - k * σ < p) (hpb : p ≤ μ + σ / k) :
    ((twoPoint μ σ k) (Set.Ici p)).toReal = 1 - 1 / (1 + k ^ 2) := by
  rw [dfp_twoPoint_real _ _ _ hk _ measurableSet_Ici,
    Set.indicator_of_notMem (by simp; linarith), Set.indicator_of_mem (by simp; linarith)]
  simp

lemma dfp_L_eq (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) :
    (μ - kStar (tau c μ σ) * σ - c) * (1 - 1 / (1 + kStar (tau c μ σ) ^ 2)) = lowerL c μ σ := by
  have ht0 : 0 ≤ tau c μ σ := div_nonneg (by linarith) hσ.le
  obtain ⟨hkle, hle2, _⟩ := kStar_le c μ σ hc hcμ hσ
  have htσ : tau c μ σ * σ = μ - c := by unfold tau; field_simp
  set t := tau c μ σ with ht
  set K := kStar t with hK
  rcases ht0.lt_or_eq with htp | hteq
  · have h5 := (eq_OA_5 t htp).2.2.2
    unfold phi at h5
    rw [← hK] at h5
    unfold lowerL
    rw [← ht, ← hK, ← h5]
    rw [show μ = t * σ + c by linarith]
    field_simp
    ring
  · have hK0 : K = 0 := by
      have hk0 : 0 ≤ K := (eq_OA_4_cardano t ht0).2.2.2.2
      have : K ≤ 2 * t / 3 := hkle
      rw [← hteq] at this; linarith
    unfold lowerL
    rw [← ht, ← hK, hK0]
    have : μ = c := by rw [← hteq] at htσ; linarith
    rw [this]; ring

lemma dfp_kσ_lt (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hμ : 0 < μ) (hσ : 0 < σ) :
    kStar (tau c μ σ) * σ < μ := by
  obtain ⟨hkle, _, _⟩ := kStar_le c μ σ hc hcμ hσ
  have htσ : tau c μ σ * σ = μ - c := by unfold tau; field_simp
  have : kStar (tau c μ σ) * σ ≤ 2 * tau c μ σ / 3 * σ := mul_le_mul_of_nonneg_right hkle hσ.le
  nlinarith

theorem solution (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hμ : 0 < μ) (hσ : 0 < σ) :
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), twoPoint μ σ (kStar (tau c μ σ) + ε) ∈ valClass μ σ) ∧
    Tendsto (fun ε : ℝ => profit c (pStar c μ σ) (twoPoint μ σ (kStar (tau c μ σ) + ε)))
      (𝓝[>] 0) (𝓝 (lowerL c μ σ)) := by
  have ht0 : 0 ≤ tau c μ σ := div_nonneg (by linarith) hσ.le
  have hk0 : 0 ≤ kStar (tau c μ σ) := (eq_OA_4_cardano (tau c μ σ) ht0).2.2.2.2
  have hlt := dfp_kσ_lt c μ σ hc hcμ hμ hσ
  set K := kStar (tau c μ σ) with hK
  set δ := (μ - K * σ) / σ with hδ
  have hδ0 : 0 < δ := div_pos (by linarith) hσ
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδ0
  have key : ∀ ε ∈ Set.Ioo (0 : ℝ) δ, 0 < K + ε ∧ (K + ε) * σ ≤ μ := by
    intro ε ⟨h1, h2⟩
    refine ⟨by linarith, ?_⟩
    have : ε * σ < μ - K * σ := by
      have := (lt_div_iff₀ hσ).1 h2; linarith
    nlinarith
  refine ⟨hev.mono fun ε hε => dfp_twoPoint_mem μ σ _ hσ (key ε hε).1 (key ε hε).2, ?_⟩
  have hcont : Continuous (fun ε : ℝ => (pStar c μ σ - c) * (1 - 1 / (1 + (K + ε) ^ 2))) := by
    have : ∀ ε : ℝ, (1 + (K + ε) ^ 2) ≠ 0 := fun ε => by positivity
    fun_prop (disch := exact this _)
  have h0 : (pStar c μ σ - c) * (1 - 1 / (1 + (K + 0) ^ 2)) = lowerL c μ σ := by
    rw [add_zero]; unfold pStar; rw [← hK]; exact dfp_L_eq c μ σ hc hcμ hσ
  have hT := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rw [h0] at hT
  refine hT.congr' ?_
  filter_upwards [hev] with ε hε
  obtain ⟨hε1, hε2⟩ := key ε hε
  unfold profit
  rw [dfp_twoPoint_Ici_eq μ σ (K + ε) (pStar c μ σ) hε1]
  · unfold pStar; rw [← hK]; nlinarith [hε.1]
  · unfold pStar; rw [← hK]
    have : 0 < σ / (K + ε) := div_pos hσ hε1
    nlinarith
