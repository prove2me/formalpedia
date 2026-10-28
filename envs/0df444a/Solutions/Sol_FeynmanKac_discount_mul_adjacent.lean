-- Prove2me | solution 1 for FeynmanKac.discount_mul_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:32:09.892267+00:00
-- url     : https://prove2.me/submissions/8cf54459-65c2-4ca3-9d3c-12bc405ecbb9

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Adjacent pathwise discount factors multiply. -/
theorem solution {Ω : Type*} (X : ℝ → Ω → ℝ) (V : ℝ → ℝ → ℝ)
    (t s r : ℝ) (hts : t ≤ s) (hsr : s ≤ r) (ω : Ω)
    (hInt : IntervalIntegrable (fun z => V (X z ω) z) MeasureTheory.volume t r) :
    Real.exp (-(∫ z in t..r, V (X z ω) z)) =
      Real.exp (-(∫ z in t..s, V (X z ω) z)) *
      Real.exp (-(∫ z in s..r, V (X z ω) z)) := by
  have htr : t ≤ r := le_trans hts hsr
  have htsInt : IntervalIntegrable (fun z => V (X z ω) z) MeasureTheory.volume t s :=
    hInt.mono_set (by
      simpa only [Set.uIcc_of_le hts, Set.uIcc_of_le htr] using
        (Set.Icc_subset_Icc le_rfl hsr))
  have hsrInt : IntervalIntegrable (fun z => V (X z ω) z) MeasureTheory.volume s r :=
    hInt.mono_set (by
      simpa only [Set.uIcc_of_le hsr, Set.uIcc_of_le htr] using
        (Set.Icc_subset_Icc hts le_rfl))
  have hadd :
      (∫ z in t..s, V (X z ω) z) +
        (∫ z in s..r, V (X z ω) z) =
          (∫ z in t..r, V (X z ω) z) :=
    intervalIntegral.integral_add_adjacent_intervals htsInt hsrInt
  have hneg :
      -(∫ z in t..r, V (X z ω) z) =
        -(∫ z in t..s, V (X z ω) z) +
        -(∫ z in s..r, V (X z ω) z) := by
    rw [← hadd]
    ring
  rw [hneg, Real.exp_add]
