-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:58:35.118264+00:00
-- url     : https://prove2.me/submissions/b638c02e-e7a4-448b-a3ea-506d415fc475

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Countable upper-barrier monitoring detects full shifted closed-horizon survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∀ v : ℝ≥0, v ≤ T →
      H ω + (X.X (b + v) ω - X.X b ω) ≤ a) ↔
    ∀ j : ℕ, τ j ≤ T →
      H ω + (X.X (b + τ j) ω - X.X b ω) ≤ a := by
  constructor
  · intro h j hj
    exact h (τ j) hj
  · intro h
    apply (chat04_random_reserve_shifted_upper_closed_survival_grid_iff
      X H ω a b T).mpr
    constructor
    · intro n hn k hkT
      obtain ⟨j, hj⟩ := hCover n hn k
      have hjT : τ j ≤ T := by
        simpa only [hj] using hkT.le
      have hjBound := h j hjT
      simpa only [hj] using hjBound
    · obtain ⟨j, hj⟩ := hTerminal
      have hjT : τ j ≤ T := by
        rw [hj]
      have hjBound := h j hjT
      simpa only [hj] using hjBound
