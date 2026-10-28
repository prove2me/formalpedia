-- Prove2me | solution 1 for AvramDividend.Classical.bv_iid_pair_half_sum_weighted_integral_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T11:54:43.448185+00:00
-- url     : https://prove2.me/submissions/313c476c-f78a-4416-ad5d-3189c427b397

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Exchangeability divides an integrable sum-weighted reward equally. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (g : ℝ → ℝ)
    (hFirst : Integrable
      (fun z : ℝ × ℝ => z.1 * g (z.1 + z.2)) (μ.prod μ))
    (hSecond : Integrable
      (fun z : ℝ × ℝ => z.2 * g (z.1 + z.2)) (μ.prod μ)) :
    2 * (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2) ∂(μ.prod μ)) =
      ∫ z : ℝ × ℝ, (z.1 + z.2) * g (z.1 + z.2) ∂(μ.prod μ) := by
  have hswap :=
    MeasureTheory.integral_prod_swap (μ := μ) (ν := μ)
      (f := fun z : ℝ × ℝ => z.1 * g (z.1 + z.2))
  have hEq :
      (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2) ∂(μ.prod μ)) =
      ∫ z : ℝ × ℝ, z.2 * g (z.1 + z.2) ∂(μ.prod μ) := by
    simpa [Prod.swap, add_comm] using hswap.symm
  calc
    2 * (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2) ∂(μ.prod μ)) =
      (∫ z : ℝ × ℝ, z.1 * g (z.1 + z.2) ∂(μ.prod μ)) +
      (∫ z : ℝ × ℝ, z.2 * g (z.1 + z.2) ∂(μ.prod μ)) := by
        rw [← hEq]
        ring
    _ = ∫ z : ℝ × ℝ,
        (z.1 * g (z.1 + z.2) + z.2 * g (z.1 + z.2)) ∂(μ.prod μ) := by
      rw [integral_add hFirst hSecond]
    _ = ∫ z : ℝ × ℝ,
        (z.1 + z.2) * g (z.1 + z.2) ∂(μ.prod μ) := by
      congr 1
      funext z
      ring
