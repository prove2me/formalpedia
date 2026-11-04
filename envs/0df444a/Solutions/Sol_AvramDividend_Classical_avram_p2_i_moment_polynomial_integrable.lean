-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_polynomial_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:37:26.220311+00:00
-- url     : https://prove2.me/submissions/eab29dba-522e-4bbe-9e45-045ee9fb3a11

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem solution
    (μ : Measure ℝ) (p : Polynomial ℝ)
    (hmom : ∀ k : ℕ, Integrable (fun z : ℝ => z ^ k) μ) :
    Integrable (fun z : ℝ => p.eval z) μ := by
  classical
  have heval (z : ℝ) :
      p.eval z = ∑ k ∈ p.support, p.coeff k * z ^ k := by
    rw [Polynomial.eval_eq_sum]
    rfl
  have hsum :
      Integrable (fun z : ℝ => ∑ k ∈ p.support, p.coeff k * z ^ k) μ := by
    apply integrable_finset_sum
    intro k hk
    exact (hmom k).const_mul _
  simpa only [← heval] using hsum
