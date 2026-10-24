-- Prove2me | solution 1 for AvramDividend.Classical.esscher_decay_of_survival_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T16:36:34.111545+00:00
-- url     : https://prove2.me/submissions/83f3645e-87fc-4838-a724-60a6374cde1f

import Theorems.Thm_AvramDividend_Classical_tilted_monotone_implies_exit_decay
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Data.ENNReal.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
A survival-law representation of the Esscher-normalised scale function
implies the full exponential comparison. The representation is the
remaining stochastic input, to be supplied by change of measure.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ)
    (W : ℝ → ℝ) (φ K : ℝ) (hK : 0 ≤ K)
    (hfinite : ∀ x : ℝ, 0 < x →
      P {ω | ∀ t : ℝ≥0, 0 ≤ x + Z t ω} ≠ ⊤)
    (hrep : ∀ x : ℝ, 0 < x →
      Real.exp (-φ * x) * W x =
        K * (P {ω | ∀ t : ℝ≥0, 0 ≤ x + Z t ω}).toReal) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by
  apply AvramDividend.Classical.tilted_monotone_implies_exit_decay W φ
  intro x hx y hy hxy
  change Real.exp (-φ * x) * W x ≤ Real.exp (-φ * y) * W y
  rw [hrep x hx, hrep y hy]
  apply mul_le_mul_of_nonneg_left ?_ hK
  apply ENNReal.toReal_mono (hfinite y hy)
  apply measure_mono
  intro ω hω
  change ∀ t : ℝ≥0, 0 ≤ y + Z t ω
  intro t
  have ht := hω t
  exact le_trans ht (add_le_add_left hxy (Z t ω))
