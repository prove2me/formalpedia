-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward57_finite_smallmark_clock_double_integral_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:01:28.943422+00:00
-- url     : https://prove2.me/submissions/2b959b60-771c-462e-8229-49a8410778cf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    (μ : Measure ℝ≥0) (hμ : μ Set.univ < ⊤)
    (ν : Measure ℝ) (B : Set ℝ)
    (hB : MeasurableSet B) (hν : ν B < ⊤)
    (hBsmall : ∀ z ∈ B, |z| ≤ 1)
    (q : ℝ) (hq : 0 ≤ q) (τ : ℝ≥0)
    (g : ℝ≥0 → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ t, |g t| ≤ M) :
    |∫ t, ∫ z,
      (if t ≤ τ ∧ z ∈ B then
        Real.exp (-(q * (t : ℝ))) * (g t * z) else 0) ∂ν ∂μ| ≤
      (M * (ν B).toReal) * (μ Set.univ).toReal := by
  classical
  let f : ℝ≥0 → ℝ → ℝ := fun t z =>
    if t ≤ τ then Real.exp (-(q * (t : ℝ))) * (g t * z) else 0
  have hfb : ∀ t ∈ (Set.univ : Set ℝ≥0), ∀ z ∈ B, |f t z| ≤ M := by
    intro t _ z hz
    by_cases hs : t ≤ τ
    · simpa [f, hs] using
        avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
          q hq t z (g t) M (hBsmall z hz) hM (hg t)
    · simp [f, hs, hM]
  have hb :=
    avram_bvb72_two_finite_source_measures_uniform_kernel_iterated_compensator_norm_le
      μ Set.univ (by measurability) hμ ν B hB hν f M hM hfb
  simp only [setIntegral_univ] at hb
  have hinner (t : ℝ≥0) :
      (∫ z, (if t ≤ τ ∧ z ∈ B then
        Real.exp (-(q * (t : ℝ))) * (g t * z) else 0) ∂ν) =
      (∫ z in B, f t z ∂ν) := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases ht : t ≤ τ <;>
      simp [Set.indicator, f, ht, and_comm, and_left_comm]
  have houter :
      (∫ t, ∫ z, (if t ≤ τ ∧ z ∈ B then
        Real.exp (-(q * (t : ℝ))) * (g t * z) else 0) ∂ν ∂μ) =
      (∫ t, ∫ z in B, f t z ∂ν ∂μ) := by
    apply integral_congr_ae
    filter_upwards [] with t
    exact hinner t
  rw [houter]
  simpa only [Real.norm_eq_abs] using hb
