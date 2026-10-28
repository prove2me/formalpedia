-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_term_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:19:53.67391+00:00
-- url     : https://prove2.me/submissions/3dc8a72a-c692-4a1d-b60e-daf643d379f5

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
open Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A summable causal Neumann correction sequence has a vanishing shifted remainder. -/
theorem solution (Q : ℕ → ℝ → ℝ)
    (hQ : ∀ x : ℝ, Summable (fun n : ℕ => Q n x)) :
    ∀ x : ℝ, Tendsto (fun n : ℕ => Q (n + 1) x)
      atTop (nhds (0 : ℝ)) := by
  intro x
  exact (hQ x).tendsto_atTop_zero.comp (tendsto_add_atTop_nat 1)
