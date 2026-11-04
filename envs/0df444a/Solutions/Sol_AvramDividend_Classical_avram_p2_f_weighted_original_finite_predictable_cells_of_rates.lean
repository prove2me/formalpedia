-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_finite_predictable_cells_of_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:07:33.200295+00:00
-- url     : https://prove2.me/submissions/ab86561c-398c-4986-9b13-e67a280b8cce

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact original-process finite predictable-cell compensation from actual
per-cell unweighted first moments, with no ν identification assumed. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H N : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (hSource : ∀ i ∈ S, ∀ ω : Ω, N i ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (s i + T i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i ∈ S, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, S.sum (fun i => H i ω * N i ω) ∂P) =
    S.sum (fun i => (∫⁻ ω, H i ω ∂P) * r i) := by
  have hFun (i : ι) (hi : i ∈ S) :
      N i = fun ω => ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (s i + T i) ×ˢ B i) := by
    funext ω
    exact hSource i hi ω
  have hMeas (i : ι) (hi : i ∈ S) : Measurable (N i) := by
    rw [hFun i hi]
    exact avram_p2_f_weighted_original_intrinsic_rectangle_measurable
      X (s i) (T i) (B i) (hB i hi)
  have hAmbient (i : ι) (hi : i ∈ S) : Measurable (H i) :=
    (hH i hi).mono (𝓕.le (s i)) le_rfl
  have hEach (i : ι) (hi : i ∈ S) :
      (∫⁻ ω, H i ω * N i ω ∂P) =
      (∫⁻ ω, H i ω ∂P) * r i := by
    calc
      (∫⁻ ω, H i ω * N i ω ∂P)
          = (∫⁻ ω, H i ω ∂P) * (∫⁻ ω, N i ω ∂P) := by
            rw [hFun i hi]
            exact avram_p2_f_weighted_original_intrinsic_future_past_product
              X (s i) (T i) (B i) (hB i hi) (H i) (hH i hi)
      _ = (∫⁻ ω, H i ω ∂P) * r i := by rw [hRate i hi]
  exact avram_p2_f_weighted_ambient_finite_lintegral_sum_from_individual_rates
    P S N H r hMeas hAmbient hEach
