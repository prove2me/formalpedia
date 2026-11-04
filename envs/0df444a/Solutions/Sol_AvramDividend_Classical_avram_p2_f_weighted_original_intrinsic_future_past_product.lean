-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_future_past_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:56:24.638622+00:00
-- url     : https://prove2.me/submissions/510a266e-4548-4984-88bb-cc81b7fb811b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original intrinsic future marked jump counts are independent in nonnegative
lintegral from genuine source-past weights, before any ν-rate identification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) ∂P) := by
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s (s + T) (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ T from zero_le)) B hB
  let Y : Ω → (ℝ≥0 → ℝ) :=
    fun ω v => X.X (s + v) ω - X.X s ω
  have hN (ω : Ω) : N ω = F (Y ω) := hExtract ω
  have hFactor :
      (∫⁻ ω, H ω * F (Y ω) ∂P) =
      (∫⁻ ω, H ω ∂P) * (∫⁻ ω, F (Y ω) ∂P) := by
    simpa only [Y] using
      (avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
        X s H hH F hF)
  change (∫⁻ ω, H ω * N ω ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P)
  calc
    (∫⁻ ω, H ω * N ω ∂P) = (∫⁻ ω, H ω * F (Y ω) ∂P) := by
      apply lintegral_congr
      intro ω
      rw [hN ω]
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, F (Y ω) ∂P) := hFactor
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P) := by
      congr 1
      apply lintegral_congr
      intro ω
      exact (hN ω).symm
