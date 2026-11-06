-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_unique_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:56:14.723181+00:00
-- url     : https://prove2.me/submissions/5e93ab8f-f441-41ac-82bf-37507b8ad1bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    ∀ i j : ℕ, i < j →
      u i < τ → u (i + 1) = τ →
      ¬ (u j < τ ∧ u (j + 1) = τ) := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun k =>
    min (((min k (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change ∀ i j : ℕ, i < j →
    u i < τ → u (i + 1) = τ →
    ¬ (u j < τ ∧ u (j + 1) = τ)
  intro i j hij hBelow hHit hNext
  have hmono : Monotone u :=
    (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).2.2
  have hij' : i + 1 ≤ j := by omega
  have hle : u (i + 1) ≤ u j := hmono hij'
  have hτle : τ ≤ u j := by simpa only [hHit] using hle
  exact (not_lt_of_ge hτle) hNext.1
