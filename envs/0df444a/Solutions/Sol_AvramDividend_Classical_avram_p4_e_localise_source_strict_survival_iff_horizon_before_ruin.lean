-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_source_strict_survival_iff_horizon_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:53:33.049985+00:00
-- url     : https://prove2.me/submissions/3d99a97d-ba5a-42fe-a561-db7a776c68a0

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact ruin-truncated clock is strictly before ruin exactly when the
    deterministic horizon is strictly before ruin. This includes infinite ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, ((τ ω : ℝ≥0∞) < ruinTime X x D ω) ↔
      ((n : ℝ≥0∞) < ruinTime X x D ω) := by
  intro ω
  rw [hτeq ω]
  have hlt : min (ruinTime X x D ω) (n : ℝ≥0∞) < ⊤ :=
    lt_of_le_of_lt (min_le_right _ _) (by simp)
  have hne : min (ruinTime X x D ω) (n : ℝ≥0∞) ≠ ⊤ :=
    ne_of_lt hlt
  rw [ENNReal.coe_toNNReal hne]
  simp [min_lt_iff]
