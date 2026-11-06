-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_strict_cap_margin_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:06:59.624887+00:00
-- url     : https://prove2.me/submissions/faf896f8-0a6a-44ce-b3b7-adf956cf73b7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_drift_cells_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (C : ℝ≥0∞)
    (ρ : ℝ) (hρ : 0 < ρ)
    (z : ℕ → ℕ → Ω → ℝ)
    (hInterior : ∀ m i (ω : Ω), i < m + 1 →
      C = ⊤ ∨ z m i ω ≤ C.toReal - ρ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ ω : Ω, ∀ i : ℕ, i < m + 1 →
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun k =>
        min (((min k (m + 1) : ℕ) : ℝ≥0) *
          (T / (m + 1))) τ
      C = ⊤ ∨ z m i ω +
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ C.toReal := by
  have hsmall :=
    avram_p3_grid3_original_ruin_stopped_physical_drift_cells_vanish
      X x D T ρ hρ
  filter_upwards [hsmall] with m hm
  intro ω i hi
  rcases hInterior m i ω hi with hTop | hMargin
  · exact Or.inl hTop
  · right
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun k =>
      min (((min k (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    have hstep :
        |(((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)| < ρ :=
      hm ω i hi
    have hle :
        (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift) ≤ ρ :=
      le_of_lt (lt_of_le_of_lt (le_abs_self _) hstep)
    linarith
