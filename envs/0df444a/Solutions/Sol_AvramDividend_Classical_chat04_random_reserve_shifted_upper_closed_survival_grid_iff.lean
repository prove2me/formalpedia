-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:49:42.629556+00:00
-- url     : https://prove2.me/submissions/6f391055-f34a-4c8b-8741-34cce5378300

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_upper_before_horizon_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Bounded upper survival through the closed horizon is an exact grid predicate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0) :
    (∀ v : ℝ≥0, v ≤ T →
      H ω + (X.X (b + v) ω - X.X b ω) ≤ a) ↔
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        H ω +
          (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω) ≤ a) ∧
    H ω + (X.X (b + T) ω - X.X b ω) ≤ a := by
  constructor
  · intro h
    refine ⟨?_, h T le_rfl⟩
    intro n hn k hgrid
    exact h _ hgrid.le
  · rintro ⟨hgrid, hTerminal⟩
    intro v hv
    rcases lt_or_eq_of_le hv with hlt | heq
    · by_contra hneg
      have habove :
          a < H ω + (X.X (b + v) ω - X.X b ω) :=
        lt_of_not_ge hneg
      obtain ⟨n, hn, k, hkt, hbad⟩ :=
        (chat04_shifted_random_reserve_upper_before_horizon_grid_iff
          X H ω a b T).mp ⟨v, hlt, habove⟩
      exact (not_lt_of_ge (hgrid n hn k hkt)) hbad
    · subst v
      exact hTerminal
