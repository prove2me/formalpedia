-- Prove2me | solution 1 for AvramDividend.Classical.avram_f16_original_physical_sigma_clock_le_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:31:24.941133+00:00
-- url     : https://prove2.me/submissions/ac85be3d-dc10-4053-bc02-82d15406ecb0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω, σ k ω ≤ (n : ℝ≥0) := by
  intro k ω
  calc
    σ k ω ≤ τ ω := hσle k ω
    _ = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := hτeq ω
    _ ≤ (n : ℝ≥0) := by
      have hc : (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal ≤
          ((n : ℝ≥0∞)).toNNReal :=
        ENNReal.toNNReal_mono (by simp) (min_le_right _ _)
      simpa using hc
