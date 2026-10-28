-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_shifted_closed_survival_schedule_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:17:41.771391+00:00
-- url     : https://prove2.me/submissions/6fb01f34-75eb-4de4-820c-f122a408ae8e

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Any rationally covering future schedule with the endpoint detects exact survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ H ω + (X.X (b + v) ω - X.X b ω)) ↔
    ∀ j : ℕ, τ j ≤ T →
      0 ≤ H ω + (X.X (b + τ j) ω - X.X b ω) := by
  constructor
  · intro h j hj
    exact h (τ j) hj
  · intro h
    apply (chat04_random_reserve_shifted_closed_survival_grid_iff
      X H ω b T).mpr
    constructor
    · intro n hn k hkT
      obtain ⟨j, hj⟩ := hCover n hn k
      have hjT : τ j ≤ T := by
        simpa only [hj] using hkT.le
      have hjSurvive := h j hjT
      simpa only [hj] using hjSurvive
    · obtain ⟨j, hj⟩ := hTerminal
      have hjT : τ j ≤ T := by
        rw [hj]
      have hjSurvive := h j hjT
      simpa only [hj] using hjSurvive
