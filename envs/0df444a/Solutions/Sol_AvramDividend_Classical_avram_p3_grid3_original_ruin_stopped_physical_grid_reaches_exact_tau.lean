-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_ruin_stopped_physical_grid_reaches_exact_tau
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:57:16.503519+00:00
-- url     : https://prove2.me/submissions/8eda7e96-f034-4f09-8a08-94b2f90f4f73

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
    u (m + 1) = τ := by
  let r : ℝ≥0∞ :=
    min (ruinTime X x D ω) (T : ℝ≥0∞)
  let τ : ℝ≥0 := r.toNNReal
  let u : ℕ → ℝ≥0 := fun k =>
    min (((min k (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1))) τ
  change u (m + 1) = τ
  have hrfinite : r < ⊤ :=
    lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top
  have hco : ((τ : ℝ≥0) : ℝ≥0∞) = r :=
    ENNReal.coe_toNNReal (ne_of_lt hrfinite)
  have hτleT : τ ≤ T := by
    have hleE : (τ : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
      rw [hco]
      exact min_le_right _ _
    exact_mod_cast hleE
  have hclock :=
    avram_p3_grid3_original_ruin_stopped_uniform_physical_clock
      X x D T m ω
  have hstop : u (m + 1) = min T τ := hclock.2.1
  calc
    u (m + 1) = min T τ := hstop
    _ = τ := min_eq_right hτleT
