-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a48_positive_exponential_tail_chernoff_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:20:56.176489+00:00
-- url     : https://prove2.me/submissions/7d6a886b-76ec-497b-a7f7-91e8e21253be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- An exponential tilt majorises the positive excursion tail of a source increment. -/
theorem solution (z θ r δ : ℝ) (hr : 0 ≤ r) :
    (if δ ≤ z then Real.exp (θ * z) else 0) ≤
      Real.exp (-r * δ) * Real.exp ((θ + r) * z) := by
  by_cases h : δ ≤ z
  · simp only [if_pos h]
    have hpos : 0 ≤ r * (z - δ) :=
      mul_nonneg hr (sub_nonneg.mpr h)
    have hle : θ * z ≤ -r * δ + (θ + r) * z := by
      nlinarith
    calc
      Real.exp (θ * z) ≤ Real.exp (-r * δ + (θ + r) * z) :=
        Real.exp_le_exp.mpr hle
      _ = Real.exp (-r * δ) * Real.exp ((θ + r) * z) :=
        Real.exp_add _ _
  · simp only [if_neg h]
    exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
