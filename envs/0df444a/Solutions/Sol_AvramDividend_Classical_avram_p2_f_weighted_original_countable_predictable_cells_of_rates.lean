-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_cells_of_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:14:58.262484+00:00
-- url     : https://prove2.me/submissions/b31606eb-074f-4a6e-910e-26b0e3fd3256

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_future_past_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Countably many genuine original Lévy marked rectangles have exact
weighted compensation from individually proved unweighted rates. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0)
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H N : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable[𝓕 (s i)] (H i))
    (hSource : ∀ i, ∀ ω : Ω, N i ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (s i + T i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, ∑' i, H i ω * N i ω ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * r i := by
  have hFun (i : ι) :
      N i = fun ω => ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (s i + T i) ×ˢ B i) := by
    funext ω
    exact hSource i ω
  have hNmeas (i : ι) : Measurable (N i) := by
    rw [hFun i]
    exact avram_p2_f_weighted_original_intrinsic_rectangle_measurable
      X (s i) (T i) (B i) (hB i)
  have hHmeas (i : ι) : Measurable (H i) :=
    (hH i).mono (𝓕.le (s i)) le_rfl
  have hEach (i : ι) :
      (∫⁻ ω, H i ω * N i ω ∂P) =
      (∫⁻ ω, H i ω ∂P) * r i := by
    calc
      (∫⁻ ω, H i ω * N i ω ∂P)
          = (∫⁻ ω, H i ω ∂P) * (∫⁻ ω, N i ω ∂P) := by
            rw [hFun i]
            exact avram_p2_f_weighted_original_intrinsic_future_past_product
              X (s i) (T i) (B i) (hB i) (H i) (hH i)
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
