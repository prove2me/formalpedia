-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_level_root_of_continuous_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T14:51:55.546992+00:00
-- url     : https://prove2.me/submissions/08c6f903-bdab-4fee-9fd6-888ee9f0ba1b

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter

/-- Continuity and unbounded increasing levels supply positive Esscher-shift roots. -/
theorem solution
    (g : ℝ → ℝ) (hg0 : g 0 = 0)
    (hcont : ContinuousOn g (Ici (0 : ℝ)))
    (htop : Tendsto g atTop atTop)
    (p : ℝ) (hp : 0 < p) :
    ∃ r : ℝ, 0 < r ∧ g r = p := by
  have hpIci : p ∈ Ici (g 0) := by
    change g 0 ≤ p
    rw [hg0]
    exact hp.le
  obtain ⟨r, hr, heq⟩ := (intermediate_value_Ici hcont htop) hpIci
  have hr0 : 0 ≤ r := hr
  have hrpos : 0 < r := by
    by_contra hn
    have hz : r = 0 := le_antisymm (le_of_not_gt hn) hr0
    subst r
    rw [hg0] at heq
    linarith
  exact ⟨r, hrpos, heq⟩
