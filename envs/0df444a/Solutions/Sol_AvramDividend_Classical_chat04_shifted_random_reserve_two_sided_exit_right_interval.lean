-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_right_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:57:50.801657+00:00
-- url     : https://prove2.me/submissions/19d1f910-c47e-45ac-85f0-da668a42578b

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_lower_exit_right_interval
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_exit_right_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strict two-sided exit after an arbitrary Lévy clock shift persists to the right. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b t : ℝ≥0)
    (h : (H ω + (X.X (b + t) ω - X.X b ω) < 0) ∨
      (a < H ω + (X.X (b + t) ω - X.X b ω))) :
    ∃ u : ℝ≥0, b + t < u ∧
      ∀ v : ℝ≥0, b + t ≤ b + v → b + v < u →
        (H ω + (X.X (b + v) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + v) ω - X.X b ω)) := by
  rcases h with hLower | hUpper
  · obtain ⟨u, hu, hPersist⟩ :=
      chat04_shifted_random_reserve_lower_exit_right_interval
        X H ω b t hLower
    refine ⟨u, hu, ?_⟩
    intro v htv hvu
    exact Or.inl (hPersist v htv hvu)
  · obtain ⟨u, hu, hPersist⟩ :=
      chat04_shifted_random_reserve_upper_exit_right_interval
        X H ω a b t hUpper
    refine ⟨u, hu, ?_⟩
    intro v htv hvu
    exact Or.inr (hPersist v htv hvu)
