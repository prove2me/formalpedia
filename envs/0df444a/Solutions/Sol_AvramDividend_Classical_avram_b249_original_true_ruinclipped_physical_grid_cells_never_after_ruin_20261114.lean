-- Prove2me | solution 1 for AvramDividend.Classical.avram_b249_original_true_ruinclipped_physical_grid_cells_never_after_ruin_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:41:30.263208+00:00
-- url     : https://prove2.me/submissions/b0dce09c-52d4-45ec-9eea-12e46bc514ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_clock_bounded_by_ruin_and_horizon_in_extended_time
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
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ω : Ω) (i : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
    (v i : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      v i ≤ (n : ℝ≥0) := by
  intro Δ v
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    intro z
    rfl
  obtain ⟨hτR, hτN⟩ :=
    avram_p4_d_dividend_original_ruin_truncated_clock_bounded_by_ruin_and_horizon_in_extended_time
      X x D n τ hτeq ω
  have hvσ : v i ≤ σ ω := min_le_right _ _
  have hστ : σ ω ≤ τ ω := hσclip ω
  have hvτ : (v i : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr (hvσ.trans hστ)
  exact ⟨hvτ.trans hτR, ENNReal.coe_le_coe.mp (hvτ.trans hτN)⟩
