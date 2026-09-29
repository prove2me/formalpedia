-- Prove2me | solution 1 for FamousTheorems.minkowski_convex_body
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:06:24.801882+00:00
-- url     : https://prove2.me/submissions/986e1d6f-d634-4fdd-92f0-2dc5b7223246

import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {F s : Set E} {L : AddSubgroup E} [Countable L]
    (fund : IsAddFundamentalDomain L F μ) (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s) (h : μ F * 2 ^ Module.finrank ℝ E < μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s :=
  MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    fund h_symm h_conv h
