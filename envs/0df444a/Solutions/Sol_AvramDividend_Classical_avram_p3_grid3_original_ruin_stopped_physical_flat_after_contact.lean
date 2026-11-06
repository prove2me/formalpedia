-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_flat_after_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:24:46.456941+00:00
-- url     : https://prove2.me/submissions/29f5dbd6-167a-4cfe-bfdc-0cd67a355104

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
    ∀ i j : ℕ, i ≤ j → u i = τ → u j = τ := by
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun k =>
    min (((min k (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change ∀ i j : ℕ, i ≤ j → u i = τ → u j = τ
  intro i j hij hHit
  have hmono : Monotone u :=
    (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).2.2
  have hτle : τ ≤ u j := by
    simpa only [hHit] using hmono hij
  have hule : u j ≤ τ := min_le_right _ _
  exact le_antisymm hule hτle
