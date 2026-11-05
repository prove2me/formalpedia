-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_original_finite_past_weight_grid_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:54:30.072147+00:00
-- url     : https://prove2.me/submissions/a783930d-963f-48a1-9486-2da7e022eda4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_weighted_from_zero_origin_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Finite original predictable count grids have their exact physical expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (N : ι → Ω → ℝ≥0∞)
    (hN : ∀ i ∈ S, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (hNm : ∀ i ∈ S, Measurable (N i))
    (W : ι → Ω → ℝ≥0∞)
    (hWp : ∀ i ∈ S, Measurable[𝓕 (s i)] (W i))
    (hWm : ∀ i ∈ S, Measurable (W i)) :
    (∫⁻ ω, ∑ i ∈ S, W i ω * N i ω ∂P) =
      ∑ i ∈ S, (∫⁻ ω, W i ω ∂P) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
  classical
  have hcell (i : ι) (hi : i ∈ S) :
      (∫⁻ ω, W i ω * N i ω ∂P) =
        (∫⁻ ω, W i ω ∂P) *
          (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)) := by
    simpa only [hN i hi] using
      (avram_p2_e_compensator_public_weighted_from_zero_origin_rate
        X (s i) (t i) (hst i hi) (B i) (hB i hi)
        (W i) (hWp i hi))
  calc
    (∫⁻ ω, ∑ i ∈ S, W i ω * N i ω ∂P) =
        ∑ i ∈ S, (∫⁻ ω, W i ω * N i ω ∂P) := by
      exact lintegral_finset_sum S (by
        intro i hi
        exact (hWm i hi).mul (hNm i hi))
    _ = _ := Finset.sum_congr rfl (by
      intro i hi
      exact hcell i hi)
