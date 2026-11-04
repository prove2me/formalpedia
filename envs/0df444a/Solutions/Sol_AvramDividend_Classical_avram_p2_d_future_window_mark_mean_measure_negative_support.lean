-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_window_mark_mean_measure_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:57:39.241459+00:00
-- url     : https://prove2.me/submissions/e688628a-952f-4bb2-adf6-03e64e841d8f

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_arbitrary_window_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every original deterministic future window has a genuine marked mean
measure supported on strictly negative jumps, with no ν-rate assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ ρ : Measure ℝ,
      (∀ (B : Set ℝ), MeasurableSet B →
        ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ B) ∂P)) ∧
      (∀ (B : Set ℝ), MeasurableSet B →
        ρ B = ρ (B ∩ Iio (0 : ℝ))) := by
  obtain ⟨ρ, hρ⟩ :=
    avram_p2_d_future_arbitrary_window_mark_mean_measure X s t hst
  refine ⟨ρ, hρ, ?_⟩
  intro B hB
  rw [hρ B hB, hρ (B ∩ Iio (0 : ℝ)) (hB.inter measurableSet_Iio)]
  apply lintegral_congr
  intro ω
  exact
    avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
      X ω s t B hB
