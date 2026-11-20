-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_strict_grid_dividend_points_pre_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:00:40.872517+00:00
-- url     : https://prove2.me/submissions/a216c87c-a9f1-4f39-8a66-ba878ce4ca83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n)
    (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (A : Ω → Finset ℝ≥0)
    (hA : ∀ ω t, t ∈ A ω → t = 0 ∨ t < ρ ω) :
    ∀ ω t, t ∈ A ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by
  have hClock :=
    (AvramDividend.Classical.avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
      X x C D hD n hn τ ρ hτeq hρle).2
  intro ω t ht
  rcases hA ω t ht with hzero | hlt
  · exact Or.inl hzero
  · have hc : (t : ℝ≥0∞) < (ρ ω : ℝ≥0∞) := by exact_mod_cast hlt
    exact Or.inr (lt_of_lt_of_le hc (hClock ω))

