-- Prove2me | solution 1 for DistFreePricing.Maximin.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:36:49.938841+00:00
-- url     : https://prove2.me/submissions/be385572-4b05-4ab9-8759-c548d52dc1a2

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting
import Theorems.Thm_DistFreePricing_Maximin_kStar_le
import Theorems.Thm_DistFreePricing_Maximin_eq_OA_4_cardano
import Theorems.Thm_DistFreePricing_Maximin_eq_OA_5
import Theorems.Thm_DistFreePricing_Maximin_theorem_1_a
import Theorems.Thm_DistFreePricing_Maximin_theorem_1_b

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

lemma dfp_L_nonneg (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) : 0 ≤ lowerL c μ σ := by
  rw [← dfp_L_eq c μ σ hc hcμ hσ]
  obtain ⟨_, _, hp⟩ := kStar_le c μ σ hc hcμ hσ
  unfold pStar at hp
  apply mul_nonneg (by linarith)
  rw [sub_nonneg]; apply div_le_one_of_le₀ (by nlinarith) (by positivity)

lemma dfp_clause2 (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hμ : 0 < μ) (hσ : 0 < σ) :
    ∀ p ε : ℝ, 0 < ε → ∃ F ∈ valClass μ σ, profit c p F < lowerL c μ σ + ε := by
  intro p ε hε
  have hL0 := dfp_L_nonneg c μ σ hc hcμ hσ
  by_cases hpc : p ≤ c
  · refine ⟨twoPoint μ σ (μ / σ), dfp_twoPoint_mem μ σ _ hσ (div_pos hμ hσ) (by
      rw [div_mul_cancel₀ _ hσ.ne']), ?_⟩
    unfold profit
    have : (p - c) * ((twoPoint μ σ (μ / σ)) (Set.Ici p)).toReal ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) ENNReal.toReal_nonneg
    linarith
  rw [not_le] at hpc
  set k0 := max ((μ - p) / σ) 0 with hk0
  have hk00 : 0 ≤ k0 := le_max_right _ _
  set g : ℝ → ℝ := fun k => (p - c) * (1 - 1 / (1 + k ^ 2)) with hg
  have hgk0 : g k0 ≤ lowerL c μ σ := by
    by_cases hpμ : μ ≤ p
    · have : k0 = 0 := by
        rw [hk0]; apply max_eq_right
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hσ.le
      simp [hg, this]; exact hL0
    · rw [not_le] at hpμ
      have hk0e : k0 = (μ - p) / σ := by
        rw [hk0]; apply max_eq_left; exact div_nonneg (by linarith) hσ.le
      have htσ : tau c μ σ * σ = μ - c := by unfold tau; field_simp
      have htp : 0 < tau c μ σ := div_pos (by linarith) hσ
      have hk0t : k0 ≤ tau c μ σ := by
        rw [hk0e]; apply div_le_div_of_nonneg_right (by linarith) hσ.le
      have h5 := (eq_OA_5 (tau c μ σ) htp).1 k0 hk00 hk0t
      have hval := (eq_OA_5 (tau c μ σ) htp).2.2.2
      have hp : p = μ - k0 * σ := by rw [hk0e]; field_simp; ring
      have e1 : g k0 = (μ - c) * phi (tau c μ σ) k0 := by
        simp only [hg]; unfold phi; rw [hp]; field_simp; linear_combination (-k0 ^ 3) * htσ
      have e2 : lowerL c μ σ = (μ - c) * phi (tau c μ σ) (kStar (tau c μ σ)) := by
        unfold lowerL; rw [hval]
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h5 (by linarith)
  have hgc : Continuous g := by
    have : ∀ k : ℝ, (1 + k ^ 2) ≠ 0 := fun k => by positivity
    simp only [hg]
    fun_prop (disch := exact this _)
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuous_iff.1 hgc k0 ε hε
  have hpos : 0 < μ - k0 * σ := by
    by_cases hpμ : μ ≤ p
    · have : k0 = 0 := by
        rw [hk0]; apply max_eq_right
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hσ.le
      rw [this]; linarith
    · rw [not_le] at hpμ
      have hk0e : k0 = (μ - p) / σ := by
        rw [hk0]; apply max_eq_left; exact div_nonneg (by linarith) hσ.le
      rw [hk0e, div_mul_cancel₀ _ hσ.ne']; linarith
  have hle_p : μ - k0 * σ ≤ p := by
    have : (μ - p) / σ ≤ k0 := le_max_left _ _
    have := (div_le_iff₀ hσ).1 this
    linarith
  set η := (μ - k0 * σ) / σ with hη
  have hη0 : 0 < η := div_pos hpos hσ
  set d := min δ η / 2 with hd
  have hd0 : 0 < d := by positivity
  have hdδ : d < δ := by
    have := min_le_left δ η; rw [hd]; linarith
  have hdη : d < η := by
    have := min_le_right δ η; rw [hd]; linarith
  set k := k0 + d with hkdef
  have hkpos : 0 < k := by linarith
  have hkμ : k * σ ≤ μ := by
    have : d * σ < μ - k0 * σ := by
      have := (lt_div_iff₀ hσ).1 hdη; linarith
    nlinarith
  refine ⟨twoPoint μ σ k, dfp_twoPoint_mem μ σ k hσ hkpos hkμ, ?_⟩
  have hap : μ - k * σ < p := by
    have : 0 < d * σ := mul_pos hd0 hσ
    nlinarith
  have hprob := dfp_twoPoint_Ici_le μ σ k p hkpos hap
  have hgk : g k < g k0 + ε := by
    have := hδg k (by rw [Real.dist_eq, hkdef]; rw [show k0 + d - k0 = d by ring, abs_of_pos hd0]; exact hdδ)
    rw [Real.dist_eq] at this
    have := (abs_lt.1 this).2
    linarith
  unfold profit
  have : (p - c) * ((twoPoint μ σ k) (Set.Ici p)).toReal ≤ g k := by
    simp only [hg]; exact mul_le_mul_of_nonneg_left hprob (by linarith)
  linarith

theorem solution (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hμ : 0 < μ) (hσ : 0 < σ) :
    0 ≤ kStar (tau c μ σ) ∧
    (∀ F ∈ valClass μ σ, lowerL c μ σ ≤ profit c (pStar c μ σ) F) ∧
    (∀ p ε : ℝ, 0 < ε → ∃ F ∈ valClass μ σ, profit c p F < lowerL c μ σ + ε) ∧
    (c < μ → ∀ F ∈ valClass μ σ, ∀ p : ℝ,
      rho c μ σ * profit c p F ≤ profit c (pStar c μ σ) F) := by
  obtain ⟨hk0, h1b⟩ := theorem_1_b c μ σ hc hcμ hσ
  refine ⟨hk0, h1b, dfp_clause2 c μ σ hc hcμ hμ hσ, ?_⟩
  intro hcμ' F hF p
  have hU := theorem_1_a c μ σ hc hcμ hσ F hF p
  have hL := h1b F hF
  have htσ : tau c μ σ * σ = μ - c := by unfold tau; field_simp
  have htp : 0 < tau c μ σ := div_pos (by linarith) hσ
  have hval := (eq_OA_5 (tau c μ σ) htp).2.1
  have hval2 := (eq_OA_5 (tau c μ σ) htp).2.2.2
  set t := tau c μ σ with ht
  set K := kStar t with hK
  have hφ0 : 0 ≤ 1 - 3 / (2 * t) * K := by
    rw [← hval2, hval]; positivity
  have hγ : gam c μ = c / μ := rfl
  have hD : 0 < 1 + gam c μ / ((1 - gam c μ) * (1 + t ^ 2)) := by
    have h1 : 0 < 1 - gam c μ := by
      rw [hγ, sub_pos, div_lt_one hμ]; exact hcμ'
    have : 0 ≤ gam c μ / ((1 - gam c μ) * (1 + t ^ 2)) :=
      div_nonneg (div_nonneg hc hμ.le) (by positivity)
    linarith
  have hρ0 : 0 ≤ rho c μ σ := by
    unfold rho; rw [← ht, ← hK]; exact div_nonneg hφ0 hD.le
  have hρU : rho c μ σ * upperU c μ σ = lowerL c μ σ := by
    unfold rho upperU lowerL
    rw [← ht, ← hK, hγ]
    have hμ0 : μ ≠ 0 := hμ.ne'
    have hmc : μ - c ≠ 0 := by linarith
    have h1t : 1 + t ^ 2 ≠ 0 := by positivity
    have hden : 1 + c / μ / ((1 - c / μ) * (1 + t ^ 2)) = (μ - c * (t ^ 2 / (1 + t ^ 2))) / (μ - c) := by
      field_simp
      ring
    rw [hden]
    have hne : μ * (1 + t ^ 2) - t ^ 2 * c ≠ 0 := by nlinarith [sq_nonneg t]
    field_simp
  calc rho c μ σ * profit c p F ≤ rho c μ σ * upperU c μ σ :=
        mul_le_mul_of_nonneg_left hU hρ0
    _ = lowerL c μ σ := hρU
    _ ≤ _ := hL
