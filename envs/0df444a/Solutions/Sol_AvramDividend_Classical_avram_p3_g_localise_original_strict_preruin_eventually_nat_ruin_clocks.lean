-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_preruin_eventually_nat_ruin_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T14:36:26.488207+00:00
-- url     : https://prove2.me/submissions/0d71bfe0-a6ef-40e8-918f-8ed9817594cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the actual original source, every strict pre-ruin time
eventually remains inside every longer natural bounded ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t : ℝ≥0∞) < ruinTime X x D ω →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (t : ℝ≥0∞) <
          (((min (ruinTime X x D ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal) : ℝ≥0∞) := by
  intro ω t hRuin
  obtain ⟨N, hN⟩ :=
    ENNReal.exists_nat_gt (show (t : ℝ≥0∞) ≠ ⊤ from ENNReal.coe_ne_top)
  have htN : t < (N : ℝ≥0) := by
    exact_mod_cast hN
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ≥0) ≤ (n : ℝ≥0) := by
    exact_mod_cast hn
  have hT : t < (n : ℝ≥0) := lt_of_lt_of_le htN hNn
  exact
    ((avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
      X x D (n : ℝ≥0)).1 ω t).mpr ⟨hRuin, hT⟩
