-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_first_moment_limit_uniform_positive_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:42:48.602082+00:00
-- url     : https://prove2.me/submissions/d9f1d883-9a22-4456-b47c-d69736bfcc80

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    (μ : ℝ → Measure ℝ) (L B : ℝ≥0∞) (hLB : L < B)
    (hmoment : Tendsto
      (fun h : ℝ => ∫⁻ z : ℝ, ENNReal.ofReal z ∂(μ h))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds L)) :
    ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0),
      ∀ R : ℝ, 0 < R →
        ENNReal.ofReal R * μ h (Ici R) ≤ B := by
  have hbound : ∀ᶠ h in nhdsWithin (0 : ℝ) (Ioi 0),
      (∫⁻ z : ℝ, ENNReal.ofReal z ∂(μ h)) < B :=
    hmoment.eventually (isOpen_Iio.mem_nhds hLB)
  have hmeas : Measurable (fun z : ℝ => ENNReal.ofReal z) := by
    fun_prop
  filter_upwards [hbound] with h hsmall R hR
  have hsubset :
      Ici R ⊆ {z : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal z} := by
    intro z hz
    exact ENNReal.ofReal_le_ofReal hz
  have hmarkov :
      ENNReal.ofReal R * μ h (Ici R) ≤
        ∫⁻ z : ℝ, ENNReal.ofReal z ∂(μ h) := by
    calc
      ENNReal.ofReal R * μ h (Ici R) ≤
          ENNReal.ofReal R *
            μ h {z : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal z} := by
        gcongr <;> exact measure_mono hsubset
      _ ≤ ∫⁻ z : ℝ, ENNReal.ofReal z ∂(μ h) := by
        simpa using MeasureTheory.mul_meas_ge_le_lintegral hmeas (ENNReal.ofReal R)
  exact hmarkov.trans (le_of_lt hsmall)
