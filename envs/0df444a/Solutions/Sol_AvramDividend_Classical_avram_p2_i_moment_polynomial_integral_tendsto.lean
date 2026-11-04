-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_polynomial_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:33:48.322106+00:00
-- url     : https://prove2.me/submissions/1c3cb9b4-fd2b-41fc-be44-427292deea04

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_finite_sum_integral_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped BigOperators

theorem solution
    {ι : Type*} (l : Filter ι)
    (μi : ι → Measure ℝ) (μ : Measure ℝ) (p : Polynomial ℝ)
    (hi : ∀ i k, Integrable (fun z : ℝ => z ^ k) (μi i))
    (hμ : ∀ k, Integrable (fun z : ℝ => z ^ k) μ)
    (hmom : ∀ k,
      Tendsto (fun i => ∫ z : ℝ, z ^ k ∂μi i) l
        (nhds (∫ z : ℝ, z ^ k ∂μ))) :
    Tendsto (fun i => ∫ z : ℝ, p.eval z ∂μi i) l
      (nhds (∫ z : ℝ, p.eval z ∂μ)) := by
  classical
  have h := AvramDividend.Classical.avram_p2_i_moment_finite_sum_integral_tendsto
    l μi μ p.support p.coeff
    (by intro i k hk; exact hi i k)
    (by intro k hk; exact hμ k)
    (by intro k hk; exact hmom k)
  have heval (z : ℝ) : p.eval z =
      ∑ k ∈ p.support, p.coeff k * z ^ k := by
    rw [Polynomial.eval_eq_sum]
    rfl
  simpa only [← heval] using h
