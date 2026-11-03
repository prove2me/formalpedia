-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:45:44.17082+00:00
-- url     : https://prove2.me/submissions/a3b3603b-87d1-4f31-86a8-692092f2964b

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-faithful original finite-grid centred martingales have a zero-mean
L² limit when their actual L² representatives are Cauchy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)] (W k i))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (W k i) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
        (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P)))
    (hCauchy : CauchySeq M) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by
  have hMean : ∀ k, (∫ ω, M k ω ∂P) = 0 := by
    intro k
    calc
      (∫ ω, M k ω ∂P) =
          ∫ ω, ∑ i ∈ Finset.range (n k),
            W k i ω * (X.X (s k i + t k i) ω - X.X (s k i) ω -
              (∫ η, X.X (t k i) η ∂P)) ∂P :=
        integral_congr_ae (hSource k)
      _ = 0 :=
        avram_wave7_06_original_finite_predictable_grid_centered_X_L1_zero
          X (n k) (s k) (t k) (W k) (hWPast k) (hWI k)
            (hXI k) (hCellI k)
  exact avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
    X M hCauchy hMean
