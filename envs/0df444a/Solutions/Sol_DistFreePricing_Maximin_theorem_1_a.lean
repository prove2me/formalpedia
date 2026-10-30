-- Prove2me | solution 1 for DistFreePricing.Maximin.theorem_1_a
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:31:24.411474+00:00
-- url     : https://prove2.me/submissions/d7e75664-b550-459e-bac6-d7a7c4bc4f2c

import Mathlib
import Definitions.Def_DistFreePricing_Maximin_Setting
import Theorems.Thm_DistFreePricing_Maximin_lemma_OA_1

open MeasureTheory DistFreePricing.Maximin

lemma dfp_cantelli_valClass (μ σ : ℝ) (hσ : 0 < σ) (F : Measure ℝ) (hF : F ∈ valClass μ σ)
    (k : ℝ) (hk : 0 ≤ k) :
    F.real (Set.Iio (μ - k * σ)) ≤ F.real (Set.Iic (μ - k * σ)) ∧
      F.real (Set.Iic (μ - k * σ)) ≤ 1 / (1 + k ^ 2) := by
  obtain ⟨hP, _, hI1, hI2, hm1, hm2⟩ := hF
  haveI := hP
  have hX : MemLp (fun v : ℝ => v) 2 F :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hI2
  have hvar : ProbabilityTheory.variance (fun v : ℝ => v) F = σ ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub hX]
    have e : ((fun v : ℝ => v) ^ 2) = (fun v : ℝ => v ^ 2) := by funext v; simp
    rw [e, hm2, hm1]; ring
  have h := (lemma_OA_1 F (fun v : ℝ => v) hX μ σ hm1 hσ.le hvar).2.2 hσ F
    ⟨hP, ‹_›, hI1, hI2, hm1, hm2⟩ k hk
  exact h

lemma dfp_real_Ici (F : Measure ℝ) [IsProbabilityMeasure F] (p : ℝ) :
    (F (Set.Ici p)).toReal = 1 - F.real (Set.Iio p) := by
  have := measureReal_compl (μ := F) (s := Set.Iio p) measurableSet_Iio
  rw [Set.compl_Iio, probReal_univ] at this
  rw [← this]; rfl

lemma dfp_ae_nonneg (F : Measure ℝ) (h0 : F (Set.Iio 0) = 0) : ∀ᵐ v ∂F, 0 ≤ v := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext a; simp
  rw [this]; exact h0

theorem solution (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) :
    ∀ F ∈ valClass μ σ, ∀ p : ℝ, profit c p F ≤ upperU c μ σ := by
  intro F hF p
  have hFc := hF
  obtain ⟨hP, h0, hI1, hI2, hm1, hm2⟩ := hF
  set t := tau c μ σ with ht
  have htσ : t * σ = μ - c := by rw [ht]; unfold tau; field_simp
  have ht0 : 0 ≤ t := div_nonneg (by linarith) hσ.le
  have hU : upperU c μ σ = μ - c + c * (1 / (1 + t ^ 2)) := by
    unfold upperU; rw [← ht]; field_simp; ring
  have hcant : F.real (Set.Iic c) ≤ 1 / (1 + t ^ 2) := by
    have := (dfp_cantelli_valClass μ σ hσ F hFc t ht0).2
    have e : μ - t * σ = c := by linarith
    rwa [e] at this
  have hUge : μ - c ≤ upperU c μ σ := by
    rw [hU]; have : 0 ≤ c * (1 / (1 + t ^ 2)) := by positivity
    linarith
  unfold profit
  by_cases hpc : p ≤ c
  · have : (p - c) * (F (Set.Ici p)).toReal ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) ENNReal.toReal_nonneg
    linarith
  rw [not_le] at hpc
  have hlhs : (p - c) * (F (Set.Ici p)).toReal = ∫ v, (Set.Ici p).indicator (fun _ => p - c) v ∂F := by
    rw [integral_indicator_const _ measurableSet_Ici, smul_eq_mul, mul_comm]; rfl
  have hint1 : Integrable (fun v : ℝ => v - c) F := hI1.sub (integrable_const c)
  have hint2 : Integrable (fun v : ℝ => (Set.Iic c).indicator (fun _ => c) v) F :=
    (integrable_const c).indicator measurableSet_Iic
  have hrhs : ∫ v, (v - c + (Set.Iic c).indicator (fun _ => c) v) ∂F
      = μ - c + F.real (Set.Iic c) * c := by
    rw [integral_add hint1 hint2, integral_sub hI1 (integrable_const c), hm1,
      integral_indicator_const _ measurableSet_Iic, integral_const, smul_eq_mul, smul_eq_mul,
      probReal_univ]; ring
  have hmono : ∫ v, (Set.Ici p).indicator (fun _ => p - c) v ∂F ≤
      ∫ v, (v - c + (Set.Iic c).indicator (fun _ => c) v) ∂F := by
    apply integral_mono_ae ((integrable_const _).indicator measurableSet_Ici) (hint1.add hint2)
    filter_upwards [dfp_ae_nonneg F h0] with v hv
    simp only [Pi.add_apply]
    by_cases h1 : v ∈ Set.Ici p
    · rw [Set.indicator_of_mem h1]
      have : 0 ≤ (Set.Iic c).indicator (fun _ => c) v := Set.indicator_nonneg (fun _ _ => hc) _
      simp only [Set.mem_Ici] at h1
      linarith
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : v ∈ Set.Iic c
      · rw [Set.indicator_of_mem h2]; linarith
      · rw [Set.indicator_of_notMem h2]
        simp only [Set.mem_Iic, not_le] at h2
        linarith
  rw [hlhs]
  calc _ ≤ _ := hmono
    _ = μ - c + F.real (Set.Iic c) * c := hrhs
    _ ≤ μ - c + c * (1 / (1 + t ^ 2)) := by nlinarith
    _ = upperU c μ σ := hU.symm
