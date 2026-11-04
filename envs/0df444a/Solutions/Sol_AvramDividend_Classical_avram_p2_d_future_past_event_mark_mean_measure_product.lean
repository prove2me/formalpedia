-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_past_event_mark_mean_measure_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:36:27.08944+00:00
-- url     : https://prove2.me/submissions/56302c83-686c-47b9-9a81-3de15db5fe94

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_arbitrary_window_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original future count restricted to any actual past event factors as
the past probability times a genuine mark measure, before ν identification. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ, ∀ (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) =
      P A * ρ B := by
  obtain ⟨ρ, hρ⟩ :=
    avram_p2_d_future_arbitrary_window_mark_mean_measure X s t hst
  refine ⟨ρ, ?_⟩
  intro B hB
  rw [avram_wave7_01_actual_intrinsic_rectangle_past_event_factor_unconditional
    X s t hst A hA B hB]
  rw [hρ B hB]