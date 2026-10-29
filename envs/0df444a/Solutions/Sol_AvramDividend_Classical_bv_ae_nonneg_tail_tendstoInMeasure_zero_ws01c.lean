-- Prove2me | solution 1 for AvramDividend.Classical.bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:06:53.054423+00:00
-- url     : https://prove2.me/submissions/77ca0d15-daf5-4ee5-bc79-b8fb8184e60f

import Mathlib
open MeasureTheory Filter Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ)
    (hNonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ f n ω)
    (hTail : ∀ a : ℝ, 0 < a →
      Tendsto (fun n => P.real {ω | a ≤ f n ω}) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop (fun _ => (0 : ℝ)) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  refine (hTail ε hε).congr fun n => ?_
  apply measureReal_congr
  filter_upwards [hNonneg n] with ω hω
  apply propext
  show ε ≤ f n ω ↔ ε ≤ dist (f n ω) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hω]
