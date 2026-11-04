-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_rational_time_uniform_mark_mean_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:48:31.704238+00:00
-- url     : https://prove2.me/submissions/3e80e547-2482-431f-8d04-85948fe57b18

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_unit_time_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_zero_origin_expected_count_rational_relation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A single original source mark measure determines every rationally related
time-window marked mean, including infinite-activity mark classes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ,
      ∀ (t : ℝ≥0) (n d : ℕ) (hd : 0 < d)
        (hrel : (d : ℝ≥0) * t = (n : ℝ≥0))
        (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 t ×ˢ B) ∂P) =
        ((n : ℝ≥0∞) / (d : ℝ≥0∞)) * ρ B := by
  obtain ⟨ρ, hρ⟩ :=
    avram_p2_d_future_original_unit_time_mark_mean_measure X
  refine ⟨ρ, ?_⟩
  intro t n d hd hrel B hB
  rw [avram_p2_d_future_zero_origin_expected_count_rational_relation
    X B hB t n d hd hrel]
  rw [hρ B hB]
