-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_upper_exit_grid_history_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:28:29.704989+00:00
-- url     : https://prove2.me/submissions/2268b89e-bccf-45ad-9557-5661d7a2ca26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- Survival of a source Levy reserve through the upper exit and in
a right-hand positive window implies eventual survival through every
convergent sampled stopping horizon, including continuous history. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (τ : ℝ≥0)
    (t : ℕ → ℝ≥0)
    (ht : Tendsto t atTop (nhds τ))
    (hBefore : ∀ s : ℝ≥0, s ≤ τ → 0 ≤ x + X.X s ω)
    (hAfter : ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ s : ℝ≥0, τ ≤ s → s < τ + δ → 0 ≤ x + X.X s ω) :
    ∀ᶠ n in atTop, ∀ s : ℝ≥0,
      s ≤ t n → 0 ≤ x + X.X s ω := by
  obtain ⟨δ, hδ, hRight⟩ := hAfter
  have hτδ : τ < τ + δ := lt_add_of_pos_right τ hδ
  have hClose : ∀ᶠ n in atTop, t n < τ + δ := by
    exact ht.eventually (isOpen_Iio.mem_nhds hτδ)
  filter_upwards [hClose] with n hn s hs
  by_cases hle : s ≤ τ
  · exact hBefore s hle
  · exact hRight s (le_of_lt (lt_of_not_ge hle))
      (lt_of_le_of_lt hs hn)
