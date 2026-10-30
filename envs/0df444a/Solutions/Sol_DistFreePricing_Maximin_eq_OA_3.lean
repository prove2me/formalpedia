-- Prove2me | solution 1 for DistFreePricing.Maximin.eq_OA_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T20:30:24.647769+00:00
-- url     : https://prove2.me/submissions/40c1bd91-cf47-4c77-a1a6-1aa9f73e35fd

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

theorem solution (c μ σ : ℝ) (hc : 0 ≤ c) (hcμ : c ≤ μ) (hσ : 0 < σ) (k : ℝ) (hk0 : 0 ≤ k)
    (hkτ : k ≤ tau c μ σ) :
    ∀ F ∈ valClass μ σ, (μ - k * σ - c) * (1 - 1 / (1 + k ^ 2)) ≤ profit c (μ - k * σ) F := by
  intro F hF
  have hP := hF.1
  obtain ⟨h1, h2⟩ := dfp_cantelli_valClass μ σ hσ F hF k hk0
  unfold profit
  rw [dfp_real_Ici]
  have hpc : 0 ≤ μ - k * σ - c := by
    have : k * σ ≤ tau c μ σ * σ := mul_le_mul_of_nonneg_right hkτ hσ.le
    have htσ : tau c μ σ * σ = μ - c := by unfold tau; field_simp
    linarith
  apply mul_le_mul_of_nonneg_left _ hpc
  linarith
