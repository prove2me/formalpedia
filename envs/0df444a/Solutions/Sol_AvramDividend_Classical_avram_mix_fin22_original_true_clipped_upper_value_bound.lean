-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin22_original_true_clipped_upper_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:30:35.185197+00:00
-- url     : https://prove2.me/submissions/7792d1f4-d18c-4592-a344-36d30743ee54

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_original_strict_pre_upper_clock_value_le
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_le_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) (hb : 0 < b)
    (ω : Ω) (ρ : ℝ≥0) :
    X.X ((min (ρ : ℝ≥0∞) (twoSidedExitUpTime X b ω)).toNNReal) ω ≤ b := by
  let τ : ℝ≥0∞ := twoSidedExitUpTime X b ω
  by_cases hρ : (ρ : ℝ≥0∞) < τ
  · have hmin : min (ρ : ℝ≥0∞) τ = (ρ : ℝ≥0∞) :=
      min_eq_left (le_of_lt hρ)
    change X.X ((min (ρ : ℝ≥0∞) τ).toNNReal) ω ≤ b
    rw [hmin]
    simpa using
      (avram_mix_fin22_original_strict_pre_upper_clock_value_le X b ω ρ hρ)
  · have hτle : τ ≤ (ρ : ℝ≥0∞) := le_of_not_gt hρ
    have hτne : τ ≠ ⊤ := by
      intro htop
      have htopLe : (⊤ : ℝ≥0∞) ≤ (ρ : ℝ≥0∞) := by
        simpa [htop] using hτle
      exact ENNReal.coe_ne_top (top_unique htopLe)
    change X.X ((min (ρ : ℝ≥0∞) τ).toNNReal) ω ≤ b
    rw [min_eq_right hτle]
    apply firstUpcrossing_value_le_threshold X b (le_of_lt hb) ω τ.toNNReal
    change (τ.toNNReal : ℝ≥0∞) = τ
    exact ENNReal.coe_toNNReal hτne
