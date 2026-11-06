-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_cells_eventually_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:42:39.209706+00:00
-- url     : https://prove2.me/submissions/af990335-8e4d-4776-a7f4-134349842fd3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_cell_size_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
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
    (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ ω : Ω, ∀ i : ℕ, i < m + 1 →
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun j =>
        min (((min j (m + 1) : ℕ) : ℝ≥0) *
          (T / (m + 1))) τ
      ((u (i + 1) - u i : ℝ≥0) : ℝ) < δ := by
  have hrate := avram_p3_grid3_uniform_physical_cell_size_tendsto_zero T δ hδ
  filter_upwards [hrate] with m hm
  intro ω i hi
  have hcell :=
    avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
      X x D T m i hi ω
  have hle :
      ((min (((min (i + 1) (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1)))
        ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) -
       min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1)))
        ((min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) : ℝ≥0) : ℝ) ≤
      ((T / (m + 1 : ℝ≥0) : ℝ≥0) : ℝ) := by
    exact_mod_cast hcell
  have hmTmp := hm
  simp only [Nat.cast_add, Nat.cast_one] at hmTmp
  exact lt_of_le_of_lt hle hmTmp
