-- Prove2me | solution 1 for AvramDividend.Classical.chat04_shifted_random_reserve_two_sided_before_horizon_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:57:55.325399+00:00
-- url     : https://prove2.me/submissions/dcbdd531-6521-4c86-bca0-bc9248167f06

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_lower_before_horizon_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_before_horizon_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strict two-sided shifted exit before a horizon has a rational grid witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0) :
    (∃ v : ℝ≥0, v < T ∧
      ((H ω + (X.X (b + v) ω - X.X b ω) < 0) ∨
        (a < H ω + (X.X (b + v) ω - X.X b ω)))) ↔
    ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T ∧
      ((H ω +
        (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω) < 0) ∨
        (a < H ω +
          (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω))) := by
  constructor
  · rintro ⟨v, hvT, hExit⟩
    rcases hExit with hLower | hUpper
    · obtain ⟨n, hn, k, hkT, hkLower⟩ :=
        (chat04_random_reserve_shifted_lower_before_horizon_grid_iff
          X H ω b T).mp ⟨v, hvT, hLower⟩
      exact ⟨n, hn, k, hkT, Or.inl hkLower⟩
    · obtain ⟨n, hn, k, hkT, hkUpper⟩ :=
        (chat04_shifted_random_reserve_upper_before_horizon_grid_iff
          X H ω a b T).mp ⟨v, hvT, hUpper⟩
      exact ⟨n, hn, k, hkT, Or.inr hkUpper⟩
  · rintro ⟨n, hn, k, hkT, hExit⟩
    exact ⟨(k : ℝ≥0) * (n : ℝ≥0)⁻¹, hkT, hExit⟩
