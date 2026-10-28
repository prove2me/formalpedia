-- Prove2me | solution 1 for AvramDividend.Classical.cofinal_nat_horizons_of_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:02:39.548985+00:00
-- url     : https://prove2.me/submissions/1c8a0ec4-9c9c-4e0d-99f6-344d3e60433d

import Mathlib.Data.NNReal.Defs
import Mathlib.Topology.UniformSpace.Real
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.AtTopBot.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped NNReal Topology

theorem solution
    (horizons : ℕ → ℝ≥0)
    (hlim : Filter.Tendsto horizons Filter.atTop (nhds 0)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε := by
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, horizons n < ε :=
    hlim.eventually_lt_const hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  exact ⟨N, le_of_lt (hN N le_rfl)⟩
