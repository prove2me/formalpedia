-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:36:21.276711+00:00
-- url     : https://prove2.me/submissions/662fd918-62f0-4710-9406-815a939cebf1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_subordinate_clock_le_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω) :
    (∀ ω, ρ ω ≤ (n : ℝ≥0)) ∧
    (∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) := by
  constructor
  · intro ω
    exact (hρle ω).trans
      (AvramDividend.Classical.avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
        X x D n τ hτeq ω)
  · exact
      AvramDividend.Classical.avram_jump6_B_original_subordinate_clock_le_ruin
        X x D n τ hτeq (fun _ => ρ)
        (by intro _ ω; exact hρle ω) 0

