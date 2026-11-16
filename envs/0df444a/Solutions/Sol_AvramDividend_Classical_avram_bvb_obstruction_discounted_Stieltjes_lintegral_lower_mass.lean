-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_discounted_Stieltjes_lintegral_lower_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:32:15.035919+00:00
-- url     : https://prove2.me/submissions/46b49d32-3de8-4427-b962-e36fa572ece8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
open scoped ENNReal
theorem solution (μ : Measure ℝ) (T : ℝ) :
    ENNReal.ofReal (Real.exp (-T)) * μ (Ioc (0 : ℝ) T) ≤
      ∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-t)) ∂μ := by
  have hmono : ∀ᵐ t ∂(μ.restrict (Ioc (0 : ℝ) T)),
      ENNReal.ofReal (Real.exp (-T)) ≤
        ENNReal.ofReal (Real.exp (-t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg ht.2))
  have h := lintegral_mono_ae hmono
  simpa only [lintegral_const, Measure.restrict_apply_univ,
    mul_comm] using h
