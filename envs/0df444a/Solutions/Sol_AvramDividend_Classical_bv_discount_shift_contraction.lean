-- Prove2me | solution 1 for AvramDividend.Classical.bv_discount_shift_contraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T13:46:02.532023+00:00
-- url     : https://prove2.me/submissions/4b7ef56d-6cb7-4bbd-a7fa-97692d2ec105

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (L : ℝ → ℝ) (δ q t : ℝ)
    (hδ : 0 < δ) (hq : 0 < q) (ht : 0 < t)
    (hL : 0 ≤ L t)
    (hsmall : q / t + L t / t < δ) :
    0 < t - q / δ ∧
      L ((t - q / δ) + q / δ) < δ * (t - q / δ) := by
  have hsum : (q + L t) / t < δ := by
    calc
      (q + L t) / t = q / t + L t / t := add_div q (L t) t
      _ < δ := hsmall
  have htotal : q + L t < δ * t :=
    (div_lt_iff₀ ht).mp hsum
  have hq_lt : q < δ * t := by linarith
  have hq_lt_ordered : q < t * δ := by nlinarith [hq_lt]
  have hdiv : q / δ < t := (div_lt_iff₀ hδ).mpr hq_lt_ordered
  have heq : (t - q / δ) + q / δ = t := by ring
  have hmul : δ * (t - q / δ) = δ * t - q := by
    field_simp [ne_of_gt hδ]
    <;> ring
  constructor
  · exact sub_pos.mpr hdiv
  · rw [heq, hmul]
    linarith
