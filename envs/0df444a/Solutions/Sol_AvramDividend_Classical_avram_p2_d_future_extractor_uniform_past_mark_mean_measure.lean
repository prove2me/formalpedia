-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_extractor_uniform_past_mark_mean_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:48:28.339197+00:00
-- url     : https://prove2.me/submissions/65090af7-a363-4fd7-b600-e4f86d5e83bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_uniform_past_mark_mean_measure_product

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original càdlàg future-path marked functional has an exact stationary
past-event mean against one genuine Borel mark measure, prior to ν-identification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ (ρ : Measure ℝ) (F : (ℝ≥0 → ℝ) → ℝ≥0∞),
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P) = P A * ρ B) := by
  obtain ⟨ρ, hρ⟩ :=
    avram_p2_d_future_uniform_past_mark_mean_measure_product X s t hst
  obtain ⟨F, hFmeas, hExact⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  refine ⟨ρ, F, hFmeas, hExact, ?_⟩
  intro A hA
  calc
    (∫⁻ ω in A, F (fun v : ℝ≥0 =>
      X.X (s + v) ω - X.X s ω) ∂P) =
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by
        apply lintegral_congr
        intro ω
        exact (hExact ω).symm
    _ = P A * ρ B := hρ A hA B hB
