-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_drift_cells_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:58:09.67721+00:00
-- url     : https://prove2.me/submissions/bd941e1f-e0c9-4d21-a284-2ecf4420afc7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_cells_eventually_small
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
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
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ ω : Ω, ∀ i : ℕ, i < m + 1 →
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun k =>
        min (((min k (m + 1) : ℕ) : ℝ≥0) *
          (T / (m + 1))) τ
      |(((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)| < ε := by
  let δ : ℝ := ε / (|X.drift| + 1)
  have hden : 0 < |X.drift| + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hsmall :=
    avram_p3_grid3_original_ruin_stopped_cells_eventually_small
      X x D T δ hδ
  filter_upwards [hsmall] with m hm
  intro ω i hi
  let τ : ℝ≥0 :=
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let u : ℕ → ℝ≥0 := fun k =>
    min (((min k (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  have hcell :
      ((u (i + 1) - u i : ℝ≥0) : ℝ) < δ :=
    hm ω i hi
  have hmono : Monotone u :=
    (avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω).2.2
  have hle : u i ≤ u (i + 1) := hmono (Nat.le_succ i)
  have hsub :
      ((u (i + 1) - u i : ℝ≥0) : ℝ) =
        (u (i + 1) : ℝ) - (u i : ℝ) := by
    exact NNReal.coe_sub hle
  have hzero : 0 ≤ ((u (i + 1) - u i : ℝ≥0) : ℝ) := by positivity
  have hlarge : |X.drift| ≤ |X.drift| + 1 := by linarith
  calc
    |(((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)| =
        ((u (i + 1) - u i : ℝ≥0) : ℝ) * |X.drift| := by
          rw [← hsub, abs_mul, abs_of_nonneg hzero]
    _ ≤ ((u (i + 1) - u i : ℝ≥0) : ℝ) * (|X.drift| + 1) :=
      mul_le_mul_of_nonneg_left hlarge hzero
    _ < δ * (|X.drift| + 1) :=
      mul_lt_mul_of_pos_right hcell hden
    _ = ε := by
      dsimp [δ]
      field_simp
