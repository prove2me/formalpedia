-- Prove2me | solution 1 for AvramDividend.Classical.nonzero_laplace_integral_eq_total_sub_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:03:07.716809+00:00
-- url     : https://prove2.me/submissions/9ca226d1-1c5d-4405-a7c0-2e8b722ef1f9

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The Laplace contribution from strictly nonzero values is the whole
    Laplace transform with its zero-atom probability removed. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → ℝ) (n : ℝ)
    (hNonzero : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) μ)
    (hZero : Integrable
      (fun ω => if D ω = 0 then (1 : ℝ) else 0) μ) :
    (∫ ω, if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω)) ∂μ) =
      (∫ ω, Real.exp (-(n * D ω)) ∂μ) -
        (∫ ω, if D ω = 0 then (1 : ℝ) else 0 ∂μ) := by
  have hSplit (ω : Ω) :
      Real.exp (-(n * D ω)) =
        (if D ω = 0 then (0 : ℝ) else Real.exp (-(n * D ω))) +
          (if D ω = 0 then (1 : ℝ) else 0) := by
    by_cases h : D ω = 0
    · simp [h]
    · simp [h]
  have hIntegral :
      (∫ ω, Real.exp (-(n * D ω)) ∂μ) =
        (∫ ω, if D ω = 0 then (0 : ℝ)
          else Real.exp (-(n * D ω)) ∂μ) +
        (∫ ω, if D ω = 0 then (1 : ℝ) else 0 ∂μ) := by
    calc
      (∫ ω, Real.exp (-(n * D ω)) ∂μ) =
          ∫ ω, ((if D ω = 0 then (0 : ℝ)
            else Real.exp (-(n * D ω))) +
            (if D ω = 0 then (1 : ℝ) else 0)) ∂μ := by
              apply integral_congr_ae
              filter_upwards with ω
              exact hSplit ω
      _ = _ := integral_add hNonzero hZero
  linarith
