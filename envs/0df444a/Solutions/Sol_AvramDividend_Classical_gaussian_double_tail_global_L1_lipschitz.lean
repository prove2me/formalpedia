-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_global_L1_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T21:11:54.306554+00:00
-- url     : https://prove2.me/submissions/06b20f36-7ae0-4ff8-bcc9-c3317623623c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_time_difference_support
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_positive_tail_L1_lipschitz

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Local time-Lipschitz control in L1 for the full Levy jump measure,
including infinite small-jump activity. -/
theorem solution (μ : Measure ℝ) (ε φ s t : ℝ)
    (hε : 0 < ε) (hφ : 0 < φ)
    (hs : ε ≤ s) (ht : ε ≤ t)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z : ℝ, ENNReal.ofReal
      (|(if 0 < t ∧ t < z then (z - t) * Real.exp (-φ * z) else 0) -
        (if 0 < s ∧ s < z then (z - s) * Real.exp (-φ * z) else 0)|) ∂μ) ≤
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) ∧
    ENNReal.ofReal (|t - s|) *
      (∫⁻ z in Ici ε, ENNReal.ofReal (Real.exp (-φ * z)) ∂μ) < ⊤ := by
  rw [gaussian_double_tail_time_difference_support μ ε φ s t hs ht]
  exact gaussian_double_tail_positive_tail_L1_lipschitz
    μ ε φ s t hε hφ hs ht hlevy
