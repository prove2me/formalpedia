-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_rectangle_past_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:28:37.952049+00:00
-- url     : https://prove2.me/submissions/25d9a304-48b4-420f-b120-9bde74b4bc8e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The literal marked count of the original Lévy process factors against
every nonnegative past weight, without assuming its jump-intensity formula. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B) :
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
  have hst : s ≤ s + T := le_add_of_nonneg_right (by positivity)
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s (s + T) hst B hB
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B)
  let Future : Ω → ℝ≥0∞ := fun ω =>
    F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
  have hEqual (ω : Ω) : N ω = Future ω := hExtract ω
  have hWeighted : (∫⁻ ω, H ω * N ω ∂P) =
      (∫⁻ ω, H ω * Future ω ∂P) := by
    apply lintegral_congr
    intro ω
    rw [hEqual ω]
  have hUnweighted : (∫⁻ ω, Future ω ∂P) =
      (∫⁻ ω, N ω ∂P) := by
    apply lintegral_congr
    intro ω
    exact (hEqual ω).symm
  have hFactor : (∫⁻ ω, H ω * Future ω ∂P) =
      (∫⁻ ω, H ω ∂P) * (∫⁻ ω, Future ω ∂P) :=
    avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
      X s H hH F hF
  change (∫⁻ ω, H ω * N ω ∂P) =
    (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P)
  calc
    _ = (∫⁻ ω, H ω * Future ω ∂P) := hWeighted
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, Future ω ∂P) := hFactor
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P) := by rw [hUnweighted]
