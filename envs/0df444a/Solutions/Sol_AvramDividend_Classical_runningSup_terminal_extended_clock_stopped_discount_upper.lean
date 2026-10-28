-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_terminal_extended_clock_stopped_discount_upper
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:17:10.657563+00:00
-- url     : https://prove2.me/submissions/d0f8d8cf-3ec7-4e37-9b6e-74e56d754065

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_terminal_extended_clock_discount_upper

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (τ : ℝ≥0∞)
    (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (ht : (t : ℝ≥0∞) ≤
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by
  exact (setLIntegral_le_lintegral _ _).trans
    (AvramDividend.Classical.runningSup_terminal_extended_clock_discount_upper X ω q b h hq hb hh u t hu ht)
