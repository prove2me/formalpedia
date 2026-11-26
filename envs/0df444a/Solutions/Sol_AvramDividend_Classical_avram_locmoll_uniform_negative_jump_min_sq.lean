-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_uniform_negative_jump_min_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:46:25.650336+00:00
-- url     : https://prove2.me/submissions/77ae255d-8aec-4f5d-b52a-acb47ef5e8e1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_generator_integrand_uniform_far_monotone_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (V : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hVmono : Monotone V) (hVnonneg : ∀ t, 0 ≤ V t)
    (hV : ContDiffOn ℝ 2 V (Ioo 0 a)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Icc l u, ∀ z < 0,
      ‖SpectrallyNegativeLevy.generatorIntegrand V x z‖ ≤ K * min 1 (z ^ 2) := by 
  obtain ⟨r, A, hr, hrle, hA, hnear⟩ :=
    avram_wave4_p3_generator_integrand_uniform_near_C2_quadratic_bound
      X V a l u hl hlu hu hV
  obtain ⟨B, hB, hfar⟩ :=
    avram_wave4_p3_generator_integrand_uniform_far_monotone_bound
      X V hVnonneg hVmono a l u r hl hlu hu hr hV
  refine ⟨max A B, hA.trans (le_max_left _ _), ?_⟩
  intro x hx z hz
  by_cases hc : z ≤ -r
  · exact (hfar x hx z hz hc).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have h1 : r ≤ 1 := hrle.trans (min_le_right _ _)
    have hz1 : z ^ 2 ≤ 1 := by
      have hzl : -1 < z := by linarith
      nlinarith [mul_nonneg (show 0 ≤ 1 + z by linarith)
        (show 0 ≤ 1 - z by linarith)]
    rw [min_eq_right hz1]
    exact (hnear x hx z ⟨lt_of_not_ge hc, hz⟩).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg z))
