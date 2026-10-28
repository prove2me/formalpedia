-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_exit_schedule_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:03:41.358639+00:00
-- url     : https://prove2.me/submissions/2cdf9295-14e4-4e25-aa96-36e6243b30a5

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_two_sided_before_horizon_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A rationally covering countable schedule detects strict two-sided exit before T. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹) :
    (∃ v : ℝ≥0, v < T ∧
      ((H ω + (X.X (b + v) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + v) ω - X.X b ω)))) ↔
    ∃ j : ℕ, τ j < T ∧
      ((H ω + (X.X (b + τ j) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + τ j) ω - X.X b ω))) := by
  constructor
  · intro h
    obtain ⟨n, hn, k, hkT, hkExit⟩ :=
      (chat04_shifted_random_reserve_two_sided_before_horizon_grid_iff
        X H ω a b T).mp h
    obtain ⟨j, hj⟩ := hCover n hn k
    refine ⟨j, ?_, ?_⟩
    · simpa only [hj] using hkT
    · simpa only [hj] using hkExit
  · rintro ⟨j, hjT, hjExit⟩
    exact ⟨τ j, hjT, hjExit⟩
