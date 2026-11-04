-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:07:33.700355+00:00
-- url     : https://prove2.me/submissions/08ebb299-11c8-4aaf-887f-01edd5762934

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_real_lintegral_conversion

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped ENNReal

theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hfinite : ∀ k, (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
    (hmom : ∀ k, Tendsto
      (fun i => ∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) l
      (nhds (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ)))
    (g : ℝ → ℝ) (hg : Continuous g)
    (hg0 : ∀ z : ℝ, z ≤ 0 ∨ 1 ≤ z → g z = 0) :
    Tendsto (fun i => ∫ z : ℝ, g z ∂μi i) l
      (nhds (∫ z : ℝ, g z ∂μ)) := by
  have hpositive_nonneg (i : ι) : ∀ᵐ z ∂μi i, 0 ≤ z :=
    (hpositive_i i).mono (fun z hz => le_of_lt hz)
  have hlimit_nonneg : ∀ᵐ z ∂μ, 0 ≤ z :=
    hunit_μ.mono (fun z hz => hz.1)
  have hreal (k : ℕ) :
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ)) := by
    have hlim :=
      (ENNReal.tendsto_toReal (hfinite k)).comp (hmom k)
    have hEq_i (i : ι) :
        (∫ z : ℝ, z ^ k ∂μi i) =
          (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i).toReal :=
      AvramDividend.Classical.avram_p2_i_moment_real_lintegral_conversion
        (μi i) (hpositive_nonneg i) k (hi i k)
    have hEq_μ :
        (∫ z : ℝ, z ^ k ∂μ) =
          (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ).toReal :=
      AvramDividend.Classical.avram_p2_i_moment_real_lintegral_conversion
        μ hlimit_nonneg k (hμ k)
    simpa only [Function.comp_def, hEq_i, hEq_μ] using hlim
  exact AvramDividend.Classical.avram_p2_i_moment_compact_test_tendsto
    l μi μ hfinite_i hfinite_μ hpositive_i hunit_μ hi hμ hreal g hg hg0
