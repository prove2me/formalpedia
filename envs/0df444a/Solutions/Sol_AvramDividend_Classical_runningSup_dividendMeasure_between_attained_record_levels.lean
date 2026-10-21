-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_between_attained_record_levels
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T19:57:30.768135+00:00
-- url     : https://prove2.me/submissions/d9545da9-6ef0-482e-8d01-1b20e65ea115

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (ω : Ω) (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b + h < X.X t ω), (t : ℝ≥0∞))) :
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (u : ℝ) (v : ℝ)) = ENNReal.ofReal h := by
  have hsu : runningSup X u ω = b := by
    have hR := firstUpcrossing_runningSup_sub_path_eq_zero
      X b hb ω u hu
    have hX := (firstUpcrossing_attains_peak X b hb ω u hu).1
    exact (sub_eq_zero.mp hR).trans hX
  have hsv : runningSup X v ω = b + h := by
    have hR := firstUpcrossing_runningSup_sub_path_eq_zero
      X (b + h) (add_nonneg hb hh) ω v hv
    have hX := (firstUpcrossing_attains_peak
      X (b + h) (add_nonneg hb hh) ω v hv).1
    exact (sub_eq_zero.mp hR).trans hX
  calc
    (dividendMeasure (runningSup X) ω)
        (Set.Ioc (u : ℝ) (v : ℝ)) =
      ENNReal.ofReal
        (runningSup X ((v : ℝ).toNNReal) ω -
         runningSup X ((u : ℝ).toNNReal) ω) :=
           runningSup_dividendMeasure_Ioc_eq_record_increment X ω _ _
    _ = ENNReal.ofReal h := by
      simp only [Real.toNNReal_coe, hsu, hsv]
      congr 1
      ring
