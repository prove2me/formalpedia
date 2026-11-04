-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_min_ruin_survival_branch_iff_horizon_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:56:31.456325+00:00
-- url     : https://prove2.me/submissions/70beedcd-9d97-47c0-a226-4ce211914dba

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Strict source terminal survival at the finite clipped clock is exactly horizon-before-ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτ : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    ∀ ω, (τ ω : ℝ≥0∞) < ruinTime X x D ω ↔
      (n : ℝ≥0∞) < ruinTime X x D ω := by
  intro ω
  have hnlt : (n : ℝ≥0∞) < ⊤ := by simp
  have hmin_lt : min (ruinTime X x D ω) (n : ℝ≥0∞) < ⊤ :=
    lt_of_le_of_lt (min_le_right _ _) hnlt
  have hcoe : (τ ω : ℝ≥0∞) =
      min (ruinTime X x D ω) (n : ℝ≥0∞) := by
    rw [hτ ω]
    exact ENNReal.coe_toNNReal (ne_of_lt hmin_lt)
  rw [hcoe]
  simp [min_lt_iff]