-- Prove2me | solution 1 for AvramDividend.Classical.chat03_tendsto_of_uniform_truncation_approximations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:07:12.887028+00:00
-- url     : https://prove2.me/submissions/1f9040ca-655b-4dd9-bbff-aa2e969b95ba

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology

/-!
A sequence converges whenever its approximating sequences converge,
and both the sequence and its limit admit arbitrarily accurate
uniform approximations at a common truncation scale.
-/
theorem solution
    {α : Type*} [PseudoMetricSpace α]
    (a : ℕ → α) (b : ℝ → ℕ → α) (L : α) (B : ℝ → α)
    (hconv : ∀ R > 0, Tendsto (b R) atTop (𝓝 (B R)))
    (happrox : ∀ ε > 0, ∃ R > 0,
      (∀ n, dist (a n) (b R n) ≤ ε) ∧ dist (B R) L ≤ ε) :
    Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he : 0 < ε / 3 := by linarith
  obtain ⟨R, hR, ha, hB⟩ := happrox (ε / 3) he
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hconv R hR))
    (ε / 3) he
  refine ⟨N, ?_⟩
  intro n hn
  calc
    dist (a n) L ≤ dist (a n) (b R n) + dist (b R n) L :=
      dist_triangle _ _ _
    _ ≤ dist (a n) (b R n) +
        (dist (b R n) (B R) + dist (B R) L) := by
          have ht := dist_triangle (b R n) (B R) L
          linarith
    _ < ε := by linarith [ha n, hN n hn, hB]
