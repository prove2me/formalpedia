-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_kernel_antitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:08:33.674601+00:00
-- url     : https://prove2.me/submissions/bcec14c0-6275-47bf-a909-a66151cf973a

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_antitone
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
open AvramDividend.Classical

/-- The integrated Gaussian Esscher double-tail is antitone on positive times. -/
theorem solution (μ : Measure ℝ) (φ s t : ℝ)
    (hs : 0 < s) (hst : s ≤ t) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) ≤
    (∫⁻ z : ℝ,
      (if 0 < s ∧ s < z then
        ENNReal.ofReal (z - s) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) := by
  apply lintegral_mono
  intro z
  exact gaussian_double_tail_atom_antitone φ s t z hs hst
