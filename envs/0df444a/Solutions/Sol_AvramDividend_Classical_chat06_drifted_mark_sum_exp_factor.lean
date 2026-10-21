-- Prove2me | solution 1 for AvramDividend.Classical.chat06_drifted_mark_sum_exp_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:03:46.639878+00:00
-- url     : https://prove2.me/submissions/4b628056-840b-4d52-80a6-c57f95e01a44

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

namespace AvramChat06

/-- For a compound-Poisson path with deterministic drift one,
its exponential moment factorises exactly into the fixed
deterministic drift moment and the marked-jump exponential
moment. This holds even if the entire Poisson jump process has
only been specified by its random count and marked prefix sum. -/
theorem integral_exp_drifted_mark_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (t θ : ℝ) :
    (∫ ω, Real.exp (θ *
        (t + ∑ j ∈ Finset.range (N ω), Y j ω)) ∂P) =
      Real.exp (θ * t) *
        (∫ ω, Real.exp (θ *
          ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) := by
  have hPoint :
      (fun ω => Real.exp (θ *
        (t + ∑ j ∈ Finset.range (N ω), Y j ω))) =
      (fun ω => Real.exp (θ * t) *
        Real.exp (θ * ∑ j ∈ Finset.range (N ω), Y j ω)) := by
    funext ω
    rw [mul_add, Real.exp_add]
  rw [hPoint, integral_const_mul]

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (t θ : ℝ) :
    (∫ ω, Real.exp (θ *
        (t + ∑ j ∈ Finset.range (N ω), Y j ω)) ∂P) =
      Real.exp (θ * t) *
        (∫ ω, Real.exp (θ *
          ∑ j ∈ Finset.range (N ω), Y j ω) ∂P) := by
  exact integral_exp_drifted_mark_sum P N Y t θ
