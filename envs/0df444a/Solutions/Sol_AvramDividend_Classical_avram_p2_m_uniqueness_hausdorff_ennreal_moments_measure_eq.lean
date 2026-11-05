-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_hausdorff_ennreal_moments_measure_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:24:49.392238+00:00
-- url     : https://prove2.me/submissions/0ebcdd8d-2c42-4e52-9340-95f1ae021e60

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_all_lintegral_tendsto_real
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_polynomial_integral_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_polynomial_moments_identify_continuous_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal

/-- Exact finite ENNReal Hausdorff moment uniqueness, including endpoints
and all Borel sets, through the already proved polynomial bridge. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [μ.Regular] [ν.Regular]
    (hμ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hν : ∀ᵐ z ∂ν, z ∈ Set.Icc (0 : ℝ) 1)
    (hmonoμ : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) μ)
    (hmonoν : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) ν)
    (hfiniteν : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν) ≠ ⊤)
    (hmom : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) =
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)) :
    μ = ν := by
  have hpμ : ∀ᵐ z ∂μ, 0 ≤ z :=
    hμ.mono (by intro z hz; exact hz.1)
  have hpν : ∀ᵐ z ∂ν, 0 ≤ z :=
    hν.mono (by intro z hz; exact hz.1)
  have hconv : ∀ k, Tendsto (fun _ : ℕ =>
        ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)
        ((Filter.atTop : Filter ℕ))
        (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂ν)) := by
    intro k
    rw [← hmom k]
    exact tendsto_const_nhds
  have hreal := avram_p2_i_moment_all_lintegral_tendsto_real
    ((Filter.atTop : Filter ℕ)) (fun _ : ℕ => μ) ν
    (by intro i; exact hpμ) hpν
    (by intro i k; exact hmonoμ k) hmonoν hfiniteν hconv
  have hrealeq : ∀ k : ℕ, (∫ z : ℝ, z ^ k ∂μ) =
      (∫ z : ℝ, z ^ k ∂ν) := by
    intro k
    exact tendsto_nhds_unique tendsto_const_nhds (hreal k)
  have hpoly : ∀ p : Polynomial ℝ,
      Integrable (fun x : ℝ => p.eval x) μ ∧
      Integrable (fun x : ℝ => p.eval x) ν ∧
      (∫ x, p.eval x ∂μ) = (∫ x, p.eval x ∂ν) := by
    intro p
    refine ⟨avram_p2_i_moment_polynomial_integrable μ p hmonoμ,
      avram_p2_i_moment_polynomial_integrable ν p hmonoν, ?_⟩
    have hto : Tendsto (fun _ : ℕ => ∫ x : ℝ, p.eval x ∂μ)
        ((Filter.atTop : Filter ℕ))
        (nhds (∫ x : ℝ, p.eval x ∂ν)) := by
      apply avram_p2_i_moment_polynomial_integral_tendsto
        ((Filter.atTop : Filter ℕ)) (fun _ : ℕ => μ) ν p
        (by intro i k; exact hmonoμ k) hmonoν
      intro k
      rw [← hrealeq k]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique tendsto_const_nhds hto
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  exact AvramDividend.Classical.avram_p2_b_rate_polynomial_moments_identify_continuous_tests
    μ ν hμ hν (fun x : ℝ => f x) f.continuous.continuousOn
    (f.integrable) (f.integrable) hpoly
