-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_predictable_integral_from_rates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:57:40.568029+00:00
-- url     : https://prove2.me/submissions/3fae1c7d-3204-456b-ad0a-36d933c749e9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_countable_st_cells_of_rates

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Expected genuine source intrinsic jump-measure integral of a countable
predictable-simple marked integrand, from separately proved original rates. -/
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
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc (s i) (t i) ×ˢ B i))
    (r : ι → ℝ≥0∞)
    (hRate : ∀ i, (∫⁻ ω, N i ω ∂P) = r i) :
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
    ∑' i, (∫⁻ ω, H i ω ∂P) * r i := by
  calc
    (∫⁻ ω, (∫⁻ p, ∑' i, (Ioc (s i) (t i) ×ˢ B i).indicator (fun _ => H i ω) p ∂((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) =
        (∫⁻ ω, ∑' i, H i ω * N i ω ∂P) := by
          congr 1
          funext ω
          rw [avram_p2_f_weighted_original_intrinsic_countable_simple_pathwise
            X s t B hB H ω]
          congr 1
          funext i
          rw [hSource i ω]
    _ = ∑' i, (∫⁻ ω, H i ω ∂P) * r i :=
      avram_p2_f_weighted_original_countable_st_cells_of_rates
        X s t hst B hB H N hH hSource r hRate
