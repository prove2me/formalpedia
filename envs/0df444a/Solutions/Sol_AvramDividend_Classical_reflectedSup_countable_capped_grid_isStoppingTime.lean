-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_countable_capped_grid_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:48:33.079443+00:00
-- url     : https://prove2.me/submissions/b04271ad-bf2a-473d-9254-72318f239dee

import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
import Theorems.Thm_AvramDividend_Classical_countable_capped_grid_superlevel_isStoppingTime
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous]
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0) (H : ℝ≥0)
    (hclock : ∀ n : ℕ, clock n ≤ H) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      ⨅ n : ℕ, if x ≤ reflectedSup X (clock n) ω
        then (clock n : WithTop ℝ≥0) else (H : WithTop ℝ≥0)) := by
  exact countable_capped_grid_superlevel_isStoppingTime
    (fun t : ℝ≥0 => fun ω : Ω => reflectedSup X t ω)
    (reflectedSup_adapted X) clock H hclock x
