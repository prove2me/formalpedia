-- Prove2me | solution 2 for FiniteEnergyPlane.monotoneOn_div_rpow_of_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T23:01:45.053495+00:00
-- url     : https://prove2.me/submissions/7b222dd6-f7c3-43f0-8744-04970b555f66

import Mathlib
open MeasureTheory Metric Filter Topology Set

theorem solution {I I' : ℝ → ℝ} {α S : ℝ}
    (hI : ∀ s ∈ Ioo 0 S, HasDerivAt I (I' s) s)
    (hineq : ∀ s ∈ Ioo 0 S, α * I s ≤ s * I' s) :
    MonotoneOn (fun s => I s / s ^ α) (Ioo 0 S) := by
  have hd : ∀ s ∈ Ioo 0 S, HasDerivAt (fun s => I s / s ^ α)
      ((I' s * s ^ α - I s * (α * s ^ (α - 1))) / (s ^ α) ^ 2) s := by
    intro s hs
    exact (hI s hs).div (Real.hasDerivAt_rpow_const (Or.inl hs.1.ne'))
      (Real.rpow_pos_of_pos hs.1 _).ne'
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 S)
    (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt) ?_
  intro s hs
  rw [interior_Ioo] at hs
  have h0 := hs.1
  apply div_nonneg _ (sq_nonneg _)
  have : s ^ α = s * s ^ (α - 1) := by
    rw [Real.rpow_sub h0, Real.rpow_one]; field_simp
  rw [this]
  have hp := Real.rpow_pos_of_pos h0 (α - 1)
  nlinarith [hineq s hs, mul_le_mul_of_nonneg_left (hineq s hs) hp.le]
