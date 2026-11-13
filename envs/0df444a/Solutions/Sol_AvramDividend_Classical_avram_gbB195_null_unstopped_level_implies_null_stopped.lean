-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB195_null_unstopped_level_implies_null_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:36:30.970503+00:00
-- url     : https://prove2.me/submissions/64822304-f67a-44e4-abcb-fd7a3af9dcf9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Null occupation remains null on any shorter, sample-dependent time region. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ → ℝ) (n : ℕ) (b : ℝ)
    (hFull : ∀ᵐ ω ∂P,
      volume {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ Y ω t = b} = 0)
    (ρ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧ Y ω t = b} = 0 := by
  filter_upwards [hFull] with ω hω
  apply le_antisymm
  · calc
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧ Y ω t = b} ≤
          volume {t : ℝ |
            0 < t ∧ t < (n : ℝ) ∧ Y ω t = b} := by
            apply measure_mono
            intro t ht
            exact ⟨ht.1, ht.2.1, ht.2.2.2⟩
      _ = 0 := hω
  · exact bot_le
