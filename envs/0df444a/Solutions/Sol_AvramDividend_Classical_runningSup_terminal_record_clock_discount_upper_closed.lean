-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_terminal_record_clock_discount_upper_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:08:32.745275+00:00
-- url     : https://prove2.me/submissions/b61af553-2d40-400d-a9c1-7d6f5147b981

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_terminal_partial_record_clock_discount_upper
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
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
    (ht : t ≤ v) :
    (∫⁻ r,
      if r ∈ Set.Ioc (u : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (u : ℝ)))) * ENNReal.ofReal h := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · exact runningSup_terminal_partial_record_clock_discount_upper
      X ω q b h hq hb hh u v t hu hv hlt
  · subst t
    have hpeakU := firstUpcrossing_attains_peak X b hb ω u hu
    have hrecordU := firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
    have hSu : runningSup X u ω = b := by
      linarith [hpeakU.1]
    have hbh : 0 ≤ b + h := add_nonneg hb hh
    have hpeakV := firstUpcrossing_attains_peak X (b + h) hbh ω v hv
    have hrecordV :=
      firstUpcrossing_runningSup_sub_path_eq_zero X (b + h) hbh ω v hv
    have hSv : runningSup X v ω = b + h := by
      linarith [hpeakV.1]
    have hw : Antitone
        (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r)))) := by
      intro s r hsr
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (mul_le_mul_of_nonneg_left hsr hq)
    simpa using
      (runningSup_discounted_partial_record_cell_upper
        X ω (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
        hw (u : ℝ) (v : ℝ) b h hh
        (by simpa using hSu) (by simpa using le_of_eq hSv))
