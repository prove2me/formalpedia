-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_zero_future_canonical_leftlim_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:26:49.645206+00:00
-- url     : https://prove2.me/submissions/d3346518-6a03-453f-b51e-0aa6c4b43dcf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original zero-time future has canonical left limits everywhere. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (∀ t : ℝ≥0, ContinuousWithinAt
      (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) (Ici t) t) ∧
    (∀ u : ℝ≥0, 0 < u →
      Tendsto (fun v : ℝ≥0 => X.X v ω - X.X 0 ω)
        (𝓝[<] u)
        (𝓝 (Function.leftLim
          (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) u))) := by
  obtain ⟨hR, hL⟩ :=
    avram_wave7_01_original_shifted_future_increment_path_cadlag X ω 0
  constructor
  · simpa only [zero_add] using hR
  · intro u hu
    apply tendsto_leftLim_of_tendsto
    obtain ⟨l, hl⟩ := hL u hu
    exact ⟨l, by simpa only [zero_add] using hl⟩
