-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:11:44.29428+00:00
-- url     : https://prove2.me/submissions/29cdf122-1012-4fb6-bfc1-c10d1a451b60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_original_any_start_negative_mark_exact_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The true BV negative jump count factors against any original adapted ENNReal weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      (∫⁻ ω, H ω ∂P) *
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  let N : Ω → ℝ≥0∞ := fun ω => ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ))
  let Future : Ω → ℝ≥0∞ := fun ω =>
    F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
  have hEqual (ω : Ω) : N ω = Future ω := hExtract ω
  have hWeighted : (∫⁻ ω, H ω * N ω ∂P) =
      ∫⁻ ω, H ω * Future ω ∂P := by
    apply lintegral_congr
    intro ω
    rw [hEqual ω]
  have hUnweighted : (∫⁻ ω, Future ω ∂P) =
      ∫⁻ ω, N ω ∂P := by
    apply lintegral_congr
    intro ω
    exact (hEqual ω).symm
  have hFactor : (∫⁻ ω, H ω * Future ω ∂P) =
      (∫⁻ ω, H ω ∂P) * (∫⁻ ω, Future ω ∂P) :=
    avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
      X s H hH F hF
  have hRate : (∫⁻ ω, N ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) :=
    avram_wave7_01_bv_original_any_start_negative_mark_exact_rate
      X hBV hFinite s t hst
  change (∫⁻ ω, H ω * N ω ∂P) =
    (∫⁻ ω, H ω ∂P) *
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))
  calc
    (∫⁻ ω, H ω * N ω ∂P) =
        ∫⁻ ω, H ω * Future ω ∂P := hWeighted
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, Future ω ∂P) := hFactor
    _ = (∫⁻ ω, H ω ∂P) * (∫⁻ ω, N ω ∂P) := by rw [hUnweighted]
    _ = (∫⁻ ω, H ω ∂P) *
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))) := by rw [hRate]
    _ = (∫⁻ ω, H ω ∂P) *
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by rw [mul_assoc]
