-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_stopped_predictable_grid_L2_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:54:48.075191+00:00
-- url     : https://prove2.me/submissions/62663989-3892-44bb-a7f8-8b604bc91201

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Stopped predictable genuine-source finite-grid L² Cauchy martingale
approximants have an L¹-integrable zero-mean limit under original P. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ → ℕ) (s t : ℕ → ℕ → ℝ≥0)
    (H : ℕ → ℕ → Ω → ℝ) (τ : Ω → ℕ)
    (hWPast : ∀ k, ∀ i ∈ Finset.range (n k),
      Measurable[𝓕 (s k i)]
        (fun ω => if i < τ ω then H k i ω else 0))
    (hWI : ∀ k, ∀ i ∈ Finset.range (n k),
      Integrable (fun ω => if i < τ ω then H k i ω else 0) P)
    (hXI : ∀ k, ∀ i ∈ Finset.range (n k),
      Integrable (X.X (t k i)) P)
    (hCellI : ∀ k, ∀ i ∈ Finset.range (n k), Integrable (fun ω =>
      (if i < τ ω then H k i ω else 0) *
        (X.X (s k i + t k i) ω - X.X (s k i) ω -
          (∫ η, X.X (t k i) η ∂P))) P)
    (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hSource : ∀ k, (M k : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ i ∈ Finset.range (n k),
        (if i < τ ω then H k i ω else 0) *
          (X.X (s k i + t k i) ω - X.X (s k i) ω -
            (∫ η, X.X (t k i) η ∂P)))
    (hCauchy : CauchySeq M) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by
  exact avram_wave7_06_original_finite_grid_martingale_L2_limit_mean_zero
    X n s t (fun k i ω => if i < τ ω then H k i ω else 0)
      hWPast hWI hXI hCellI M hSource hCauchy
