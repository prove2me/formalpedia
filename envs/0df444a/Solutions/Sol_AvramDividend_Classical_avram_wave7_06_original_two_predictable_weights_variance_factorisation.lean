-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_two_predictable_weights_variance_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:31:40.842182+00:00
-- url     : https://prove2.me/submissions/f0fa9e9a-b490-4a21-b154-0912aae901b3

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_two_predictable_weighted_cells_L2_additive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact two-step scalar predictable weighted source variance factorisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s] W₀)
    (hW₁ : Measurable[𝓕 (s + u)] W₁)
    (hW₀Sq : Integrable (fun ω => (W₀ ω)^2) P)
    (hW₁Sq : Integrable (fun ω => (W₁ ω)^2) P)
    (hXI₀ : Integrable (X.X u) P)
    (hXI₁ : Integrable (X.X v) P)
    (hXSq₀ : Integrable (fun ω => (X.X u ω)^2) P)
    (hXSq₁ : Integrable (fun ω => (X.X v ω)^2) P)
    (hEarlierProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) * W₁ ω) P)
    (hSqA : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P)))^2) P)
    (hSqB : Integrable (fun ω =>
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))^2) P)
    (hCross : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) *
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))) P) :
    (∫ ω, ((W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) +
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P))))^2 ∂P) =
    (∫ ω, (W₀ ω)^2 ∂P) *
      (∫ ω, (X.X u ω - (∫ η, X.X u η ∂P))^2 ∂P) +
    (∫ ω, (W₁ ω)^2 ∂P) *
      (∫ ω, (X.X v ω - (∫ η, X.X v η ∂P))^2 ∂P) := by
  have hAdd :=
    avram_wave7_06_original_two_predictable_weighted_cells_L2_additive
      X s u v W₀ W₁ hW₀ hW₁ hXI₁ hEarlierProduct hSqA hSqB hCross
  have hA :=
    avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
      X s u W₀ hW₀ hW₀Sq hXI₀ hXSq₀
  have hB :=
    avram_wave7_06_original_predictable_weight_centered_future_increment_L2_isometry
      X (s + u) v W₁ hW₁ hW₁Sq hXI₁ hXSq₁
  rw [hAdd, hA, hB]
