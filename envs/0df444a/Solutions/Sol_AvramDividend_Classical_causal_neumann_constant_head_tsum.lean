-- Prove2me | solution 1 for AvramDividend.Classical.causal_neumann_constant_head_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T22:10:50.952886+00:00
-- url     : https://prove2.me/submissions/69682bd2-9b07-45bd-9799-9ae1a738b1a7

import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A Gaussian Neumann series with the initial constant term has the expected total sum. -/
theorem solution
    (Q H : ℕ → ℝ → ℝ) (a : ℝ) (g : ℝ → ℝ)
    (hQ : ∀ x : ℝ, Summable (fun n : ℕ => Q n x))
    (hQ0 : Q 0 = fun _ : ℝ => 1 / a)
    (hQsucc : ∀ n : ℕ, Q (n + 1) = H n)
    (hg : ∀ x : ℝ, g x = 1 / a + ∑' n : ℕ, H n x) :
    ∀ x : ℝ, g x = ∑' n : ℕ, Q n x := by
  intro x
  calc
    g x = 1 / a + ∑' n : ℕ, H n x := hg x
    _ = Q 0 x + ∑' n : ℕ, Q (n + 1) x := by
      rw [congrFun hQ0 x]
      congr 1
      exact tsum_congr (fun n => (congrFun (hQsucc n) x).symm)
    _ = ∑' n : ℕ, Q n x := (hQ x).tsum_eq_zero_add.symm
