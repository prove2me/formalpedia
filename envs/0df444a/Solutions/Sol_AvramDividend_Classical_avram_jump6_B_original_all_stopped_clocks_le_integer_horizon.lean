-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_all_stopped_clocks_le_integer_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T21:02:25.953172+00:00
-- url     : https://prove2.me/submissions/62a8ae55-8c02-405c-89cf-18a29b75857b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω, σ k ω ≤ (n : ℝ≥0) := by
  intro k ω
  have hTau := avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
    X x D n τ hτeq ω
  have hσInf : (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr (hσle k ω)
  have hBound : (σ k ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    calc
      (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := hσInf
      _ = min (ruinTime X x D ω) (n : ℝ≥0∞) := hTau
      _ ≤ (n : ℝ≥0∞) := min_le_right _ _
  exact ENNReal.coe_le_coe.mp hBound
