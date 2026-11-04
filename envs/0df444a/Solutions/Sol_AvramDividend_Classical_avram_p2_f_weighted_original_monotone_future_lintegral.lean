-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_monotone_future_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:49:29.832474+00:00
-- url     : https://prove2.me/submissions/49f6a581-eb1f-43bd-bd61-e6e29b442137

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Monotone past weight approximation respects the *original* source
intrinsic marked rectangle lintegral, including infinite values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ)
    (H K : Ω → ℝ≥0∞) (hHK : ∀ ω, H ω ≤ K ω) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) ≤
    (∫⁻ ω, K ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) ∂P) := by
  apply MeasureTheory.lintegral_mono
  intro ω
  exact mul_le_mul_of_nonneg_right (hHK ω) (zero_le)
