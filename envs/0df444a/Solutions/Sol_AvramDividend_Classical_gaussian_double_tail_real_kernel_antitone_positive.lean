-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_real_kernel_antitone_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:17:28.03853+00:00
-- url     : https://prove2.me/submissions/135389e8-7737-4e0c-add4-8930e030f261

import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_antitone
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_finite_positive
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The finite real Esscher double-tail kernel is antitone on positive times. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    AntitoneOn
      (fun t : ℝ => (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂μ).toReal)
      (Ioi (0 : ℝ)) := by
  intro s hs t ht hst
  have hfin :=
    AvramDividend.Classical.gaussian_double_tail_kernel_finite_positive
      μ φ hφ hlevy s hs
  exact ENNReal.toReal_mono (ne_top_of_lt hfin)
    (AvramDividend.Classical.gaussian_double_tail_kernel_antitone
      μ φ s t hs hst)
