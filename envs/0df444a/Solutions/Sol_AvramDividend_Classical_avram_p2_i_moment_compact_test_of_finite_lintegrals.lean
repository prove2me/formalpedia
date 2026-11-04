-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_compact_test_of_finite_lintegrals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:43:26.095594+00:00
-- url     : https://prove2.me/submissions/8ac8598b-7721-4d62-b1f8-f418c3f44954

import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_integrable_of_lintegral_ne_top
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_compact_test_of_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- High ENNReal moments provide the real integrability assumptions of the compact-test limit. -/
theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ)
    (hfinite_i : ∀ i, (μi i) Set.univ < ⊤)
    (hfinite_μ : μ Set.univ < ⊤)
    (hpositive_i : ∀ i, ∀ᵐ z ∂μi i, 0 < z)
    (hunit_μ : ∀ᵐ z ∂μ, z ∈ Set.Icc (0 : ℝ) 1)
    (hmom_i_finite : ∀ i k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μi i) ≠ ⊤)
    (hmom_μ_finite : ∀ k,
      (∫⁻ z : ℝ, (ENNReal.ofReal z) ^ k ∂μ) ≠ ⊤)
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
  have hi (i : ι) (k : ℕ) : Integrable (fun z : ℝ => z ^ k) (μi i) :=
    AvramDividend.Classical.avram_p2_i_moment_integrable_of_lintegral_ne_top
      (μi i) (hpositive_nonneg i) k (hmom_i_finite i k)
  have hμ (k : ℕ) : Integrable (fun z : ℝ => z ^ k) μ :=
    AvramDividend.Classical.avram_p2_i_moment_integrable_of_lintegral_ne_top
      μ hlimit_nonneg k (hmom_μ_finite k)
  exact AvramDividend.Classical.avram_p2_i_moment_compact_test_of_lintegral
    l μi μ hfinite_i hfinite_μ hpositive_i hunit_μ hi hμ
    hmom_μ_finite hmom g hg hg0
