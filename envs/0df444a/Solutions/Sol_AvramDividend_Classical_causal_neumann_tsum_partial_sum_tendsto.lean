-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_tsum_partial_sum_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:02:26.185702+00:00
-- url     : https://prove2.me/submissions/4ce23399-7110-4f44-b498-79416b35503d

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Pi

open Filter

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Pointwise summable Neumann corrections converge through finite prefixes. -/
theorem solution
    (Q : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hQ : ∀ x : ℝ, Summable (fun n : ℕ => Q n x))
    (hg : ∀ x : ℝ, g x = ∑' n : ℕ, Q n x) :
    ∀ x : ℝ, Tendsto
      (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), Q i) x)
      atTop (nhds (g x)) := by
  intro x
  have hsum : Tendsto
      (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), Q i x)
      atTop (nhds (∑' i : ℕ, Q i x)) :=
    (hQ x).tendsto_sum_tsum_nat.comp (tendsto_add_atTop_nat 1)
  simpa only [Finset.sum_apply, hg x] using hsum
