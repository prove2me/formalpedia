-- Prove2me | solution 1 for AvramDividend.Classical.avram_b248_original_positive_ruinclipped_clock_implies_ruin_strictly_after_zero_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:57:58.683006+00:00
-- url     : https://prove2.me/submissions/1a25e77a-f21d-4eae-ace6-5cda422427f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ω : Ω) (hσpositive : 0 < σ ω) :
    0 < ruinTime X x D ω := by
  by_contra hnot
  have hr : ruinTime X x D ω = 0 :=
    le_antisymm (le_of_not_gt hnot) bot_le
  have hs : σ ω ≤ 0 := by simpa [hr] using hσclip ω
  exact (not_le_of_gt hσpositive) hs
