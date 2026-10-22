-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_positive_double_tail_tonelli_of_levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:32:43.581118+00:00
-- url     : https://prove2.me/submissions/6f53187e-fca3-4975-a621-5901220e8c2a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_positive_restrict_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_tonelli
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Tonelli for positive Lévy jump magnitudes, with s-finiteness discharged
from the truncated-square hypothesis. -/
theorem solution
    (μ : Measure ℝ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (φ θ : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂(μ.restrict (Ioi (0 : ℝ))) ∂volume) =
    (∫⁻ z : ℝ, ∫⁻ t : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
          ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂volume ∂(μ.restrict (Ioi (0 : ℝ)))) := by
  letI : SigmaFinite (μ.restrict (Ioi (0 : ℝ))) :=
    AvramDividend.Classical.gaussian_levy_positive_restrict_sigmaFinite μ hlevy
  exact AvramDividend.Classical.gaussian_double_tail_tonelli
    (μ.restrict (Ioi (0 : ℝ))) φ θ
