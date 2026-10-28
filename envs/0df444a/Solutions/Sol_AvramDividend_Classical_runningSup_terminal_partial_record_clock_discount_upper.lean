-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_terminal_partial_record_clock_discount_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:56:21.957107+00:00
-- url     : https://prove2.me/submissions/e9163709-81a9-46c1-b7d7-0b004cadd14c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_pre_firstUpcrossing_between
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partial_record_cell_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q b h : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (u v t : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + h < X.X r ω), (r : ℝ≥0∞)))
    (ht : t < v) :
    (∫⁻ r,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by
  have hpeak := firstUpcrossing_attains_peak X b hb ω u hu
  have hrecord := firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
  have hSu : runningSup X u ω = b := by
    linarith [hpeak.1]
  have hSt : runningSup X t ω ≤ b + h :=
    (runningSup_pre_firstUpcrossing_between X (b + h) ω v hv t ht).2
  have hweight : Antitone
      (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r)))) := by
    intro s r hsr
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left hsr hq)
  simpa using
    (runningSup_discounted_partial_record_cell_upper
      X ω (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
      hweight (u : ℝ) (t : ℝ) b h hh
      (by simpa using hSu) (by simpa using hSt))
