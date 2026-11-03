-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_stopped_grid_summable_L2_tail_limit_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:55:57.695458+00:00
-- url     : https://prove2.me/submissions/0c9d3001-d440-411b-8e59-c531a3ae9996

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.UniformSpace.Cauchy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_grid_L2_limit_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- An explicit summable L² step-distance tail certificate gives a genuine
zero-mean stopped original process martingale limit. -/
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
    (hTail : Summable (fun k => dist (M k) (M (k + 1)))) :
    ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto M Filter.atTop (𝓝 L) ∧
      (∫ ω, L ω ∂P) = 0 := by
  have hCauchy : CauchySeq M := cauchySeq_of_summable_dist hTail
  exact avram_wave7_06_original_stopped_predictable_grid_L2_limit_mean_zero
    X n s t H τ hWPast hWI hXI hCellI M hSource hCauchy
