-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_st_cells_of_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:37:07.316204+00:00
-- url     : https://prove2.me/submissions/80be5f43-f7d0-4ad8-b96d-f1458f03de96

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-original (sᵢ,tᵢ] predictable marked-cell compensation for any
countable family of rectangles under separately established source means. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H N : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hSource : ∀ i, ∀ ω : Ω, N i ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * r i := by
  have hEndpoint (i : ι) : s i + (t i - s i) = t i := by
    calc
      s i + (t i - s i) = (t i - s i) + s i := add_comm _ _
      _ = t i := tsub_add_cancel_of_le (hst i)
  have hFun (i : ι) :
      N i = fun ω => ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) := by
    funext ω
    exact hSource i ω
  have hNmeas (i : ι) : Measurable (N i) := by
    rw [hFun i]
    simpa only [hEndpoint i] using
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X (s i) (t i - s i) (B i) (hB i))
  have hHmeas (i : ι) : Measurable (H i) :=
    (hH i).mono (𝓕.le (s i)) le_rfl
  have hEach (i : ι) :
      (∫⁻ ω, H i ω * N i ω ∂P) =
      (∫⁻ ω, H i ω ∂P) * r i := by
    calc
      (∫⁻ ω, H i ω * N i ω ∂P)
          = (∫⁻ ω, H i ω ∂P) * (∫⁻ ω, N i ω ∂P) := by
            rw [hFun i]
            simpa only [hEndpoint i] using
              (avram_p2_f_weighted_original_intrinsic_future_past_product
                X (s i) (t i - s i) (B i) (hB i) (H i) (hH i))
      _ = (∫⁻ ω, H i ω ∂P) * r i := by rw [hRate i]
  calc
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂P)
        = ∑' i, (∫⁻ ω, H i ω * N i ω ∂P) := by
            exact lintegral_tsum
              (fun i => ((hHmeas i).mul (hNmeas i)).aemeasurable)
    _ = ∑' i, (∫⁻ ω, H i ω ∂P) * r i := by
          congr 1
          funext i
          exact hEach i
