-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_extractor_past_event_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:52:34.859477+00:00
-- url     : https://prove2.me/submissions/66b59909-bb4f-46da-9553-3653eb6e427e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine original marked-jump future functional is independent of
every measurable event in the original past, at the level of ENNReal means. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∀ A : Set Ω, MeasurableSet[𝓕 s] A →
        (∫⁻ ω in A, F (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P) =
        P A * (∫⁻ ω, F (fun v : ℝ≥0 =>
          X.X (s + v) ω - X.X s ω) ∂P)) := by
  obtain ⟨F, hFmeas, hExact⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst B hB
  refine ⟨F, hFmeas, hExact, ?_⟩
  intro A hA
  have hPast :=
    avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
      X s t hst A hA B hB
  have hRestricted :
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
  have hFull :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      (∫⁻ ω, F (fun v : ℝ≥0 =>
        X.X (s + v) ω - X.X s ω) ∂P) := by
    apply lintegral_congr
    intro ω
    exact hExact ω
  calc
    (∫⁻ ω in A, F (fun v : ℝ≥0 =>
      X.X (s + v) ω - X.X s ω) ∂P) =
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := hRestricted
    _ = P A * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := hPast
    _ = P A * (∫⁻ ω, F (fun v : ℝ≥0 =>
      X.X (s + v) ω - X.X s ω) ∂P) :=
      congrArg (fun z : ℝ≥0∞ => P A * z) hFull