-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_atom_full_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:06:18.501+00:00
-- url     : https://prove2.me/submissions/b35bfa04-4506-42c9-8c65-e4bd6b303a5b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_weighted_atom_lintegral
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (φ z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ t : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂volume) =
      ENNReal.ofReal (Real.exp (-(φ * z))) *
        ENNReal.ofReal (z ^ 2 / 2) := by
  have hfun :
      (fun t : ℝ =>
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z))) else 0) =
      (Ioo (0 : ℝ) z).indicator
        (fun t : ℝ =>
          ENNReal.ofReal (Real.exp (-(φ * z))) *
            ENNReal.ofReal (z - t)) := by
    funext t
    by_cases ht : 0 < t ∧ t < z
    · simp [Set.indicator, ht, mul_comm]
    · simp [Set.indicator, ht]
  rw [hfun]
  calc
    (∫⁻ t : ℝ,
      (Ioo (0 : ℝ) z).indicator
        (fun t : ℝ =>
          ENNReal.ofReal (Real.exp (-(φ * z))) *
            ENNReal.ofReal (z - t)) t ∂volume) =
      (∫⁻ t in Ioo (0 : ℝ) z,
        ENNReal.ofReal (Real.exp (-(φ * z))) *
          ENNReal.ofReal (z - t) ∂volume) :=
        lintegral_indicator measurableSet_Ioo _
    _ = (∫⁻ t in Ioc (0 : ℝ) z,
        ENNReal.ofReal (Real.exp (-(φ * z))) *
          ENNReal.ofReal (z - t) ∂volume) :=
        setLIntegral_congr Ioo_ae_eq_Ioc
    _ = _ := gaussian_double_tail_weighted_atom_lintegral φ z hz
