-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_finite_NNReal_ruin_clocks_monotone_sup_actual_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:12:42.533742+00:00
-- url     : https://prove2.me/submissions/0f5d7394-4c8e-422e-aee8-2cea05ede50e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_clipped_NNReal_clocks_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact finite NNReal truncations of the true original ruin time
    increase to that ruin time, including ruin at infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτ : ∀ n ω, τ n ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) :
    (∀ ω, Monotone (fun n => τ n ω)) ∧
      (∀ ω, (⨆ n : ℕ, (τ n ω : ℝ≥0∞)) = ruinTime X x D ω) := by
  constructor
  · intro ω n m hnm
    change τ n ω ≤ τ m ω
    rw [hτ n ω, hτ m ω]
    exact (avram_p4_e_localise_original_ruin_clipped_NNReal_clocks_monotone
      X x D ω) hnm
  · intro ω
    have hfinite (n : ℕ) :
        min (ruinTime X x D ω) (n : ℝ≥0∞) ≠ ⊤ := by
      apply ne_of_lt
      exact lt_of_le_of_lt (min_le_right _ _) (by simp)
    calc
      (⨆ n : ℕ, (τ n ω : ℝ≥0∞)) =
          ⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞) := by
            apply iSup_congr
            intro n
            rw [hτ n ω, ENNReal.coe_toNNReal (hfinite n)]
      _ = ruinTime X x D ω := by
        calc
          (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) =
              ruinTime X x D ω ⊓ (⨆ n : ℕ, (n : ℝ≥0∞)) := by
                simp only [inf_iSup_eq]
          _ = ruinTime X x D ω := by
                simp [ENNReal.iSup_natCast]
