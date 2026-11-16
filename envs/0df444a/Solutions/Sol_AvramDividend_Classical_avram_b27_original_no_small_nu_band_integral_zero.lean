-- Prove2me | solution 1 for AvramDividend.Classical.avram_b27_original_no_small_nu_band_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:26:05.281211+00:00
-- url     : https://prove2.me/submissions/2acaba65-3512-4548-a0b2-4a68362df032

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ)
    (hν : ν (Ioc (-1 : ℝ) 0) = 0)
    (n : ℕ) :
    (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))),
      z ∂ν) = 0 := by
  have hn : -(1 / ((n : ℝ) + 1)) ≤ 0 := by
    have hp : 0 ≤ (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hsub : Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))) ⊆
      Ioc (-1 : ℝ) 0 := by
    intro z hz
    exact ⟨hz.1, le_trans hz.2 hn⟩
  have hnull :
      ν (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) = 0 := by
    exact measure_mono_null hsub hν
  have hRestrict :
      ν.restrict (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) = 0 :=
    Measure.restrict_eq_zero.mpr hnull
  change (∫ z, z ∂(ν.restrict
    (Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))))) = 0
  rw [hRestrict]
  simp
