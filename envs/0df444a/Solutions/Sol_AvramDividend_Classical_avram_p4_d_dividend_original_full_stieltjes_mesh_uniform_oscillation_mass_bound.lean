-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_mesh_uniform_oscillation_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:07:54.83076+00:00
-- url     : https://prove2.me/submissions/f13e4200-2ab5-4c27-a708-d6c65b1201d0

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A uniform payment-cell oscillation is bounded by the complete original mesh mass. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s : Finset ι) (a b : ι → ℝ≥0)
    (δ : ι → ℝ≥0∞) (ε : ℝ≥0∞)
    (hδ : ∀ i ∈ s, δ i ≤ ε) :
    (∑ i ∈ s, δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) ≤
      ε * (∑ i ∈ s, dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by
  calc
    (∑ i ∈ s, δ i * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) ≤
        (∑ i ∈ s, ε * dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hδ i hi) zero_le
    _ = ε * (∑ i ∈ s, dividendMeasure D ω (Ioc (a i : ℝ) (b i : ℝ))) := by
      rw [Finset.mul_sum]
