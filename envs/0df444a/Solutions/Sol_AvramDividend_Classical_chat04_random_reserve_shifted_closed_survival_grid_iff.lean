-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_shifted_closed_survival_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:10:12.021081+00:00
-- url     : https://prove2.me/submissions/9679e0a9-274c-44e2-be08-4b98dc10c74a

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_lower_before_horizon_grid_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Closed-horizon shifted future survival is precisely a rational grid plus its endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b T : ℝ≥0) :
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ H ω + (X.X (b + v) ω - X.X b ω)) ↔
    (∀ n : ℕ, 0 < n → ∀ k : ℕ,
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
        0 ≤ H ω +
          (X.X (b + (k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω - X.X b ω)) ∧
    0 ≤ H ω + (X.X (b + T) ω - X.X b ω) := by
  constructor
  · intro h
    refine ⟨?_, h T le_rfl⟩
    intro n hn k hgrid
    exact h _ hgrid.le
  · rintro ⟨hgrid, hTerminal⟩
    intro v hv
    rcases lt_or_eq_of_le hv with hlt | heq
    · by_contra hneg
      have hbelow :
          H ω + (X.X (b + v) ω - X.X b ω) < 0 :=
        lt_of_not_ge hneg
      obtain ⟨n, hn, k, hkt, hbad⟩ :=
        (chat04_random_reserve_shifted_lower_before_horizon_grid_iff
          X H ω b T).mp ⟨v, hlt, hbelow⟩
      exact (not_lt_of_ge (hgrid n hn k hkt)) hbad
    · subst v
      exact hTerminal
