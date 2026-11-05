-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_clock_bounded_by_ruin_and_horizon_in_extended_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:51:04.141553+00:00
-- url     : https://prove2.me/submissions/c8b9634b-34db-4eaf-bdad-505531d790dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal source stopped dividend clock never exceeds either the
original controlled ruin time or the chosen finite horizon, in extended
nonnegative time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω ∧
      (τ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
  intro ω
  rw [hτeq ω]
  have hcast :
      (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ≥0∞)
        ≤ min (ruinTime X x D ω) (n : ℝ≥0∞) :=
    ENNReal.coe_toNNReal_le_self
  exact ⟨hcast.trans (min_le_left _ _),
    hcast.trans (min_le_right _ _)⟩
