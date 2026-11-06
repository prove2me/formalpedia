-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_cell_length_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:18:20.344578+00:00
-- url     : https://prove2.me/submissions/282bf180-33ac-40e1-bd14-26c26ed7087a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_endpoints_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_uniform_physical_clock_exact_cell_length
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
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (m i : ℕ) (hi : i < m + 1) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    u (i + 1) - u i ≤ T / (m + 1) := by
  let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  let v : ℕ → ℝ≥0 := fun j =>
    ((min j (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
  have hv := avram_p3_grid3_uniform_physical_clock_endpoints_monotone T m
  have hvi : v i ≤ v (i + 1) := hv.2.2 (Nat.le_succ i)
  have hdiff : v (i + 1) - v i = T / (m + 1) :=
    avram_p3_grid3_uniform_physical_clock_exact_cell_length T m i hi
  change min (v (i + 1)) τ - min (v i) τ ≤ T / (m + 1)
  rcases le_total τ (v i) with hτi | hiτ
  · have hτj : τ ≤ v (i + 1) := le_trans hτi hvi
    simpa [min_eq_right hτi, min_eq_right hτj] using
      (show (0 : ℝ≥0) ≤ T / (m + 1) from zero_le _)
  · have hleft : min (v i) τ = v i := min_eq_left hiτ
    have hle : min (v (i + 1)) τ ≤ v (i + 1) := min_le_left _ _
    have hsub := tsub_le_tsub_right hle (v i)
    simpa only [hleft, hdiff] using hsub
