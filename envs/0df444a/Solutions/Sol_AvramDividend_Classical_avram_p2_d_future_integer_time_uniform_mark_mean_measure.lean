-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_integer_time_uniform_mark_mean_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:41:51.83809+00:00
-- url     : https://prove2.me/submissions/df6b582a-ddc7-4686-9be4-456841cd0c21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_unit_time_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_nat_scaling

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- One genuine original source mark measure gives the exact integer-time
expected count rates on every Borel mark set, even with infinite activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ, ∀ (n : ℕ) (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc 0 (n : ℝ≥0) ×ˢ B) ∂P) =
      (n : ℝ≥0∞) * ρ B := by
  obtain ⟨ρ, hρ⟩ :=
    avram_p2_d_future_original_unit_time_mark_mean_measure X
  refine ⟨ρ, ?_⟩
  intro n B hB
  rw [avram_p2_d_future_zero_origin_expected_count_nat_scaling X B hB n]
  rw [hρ B hB]