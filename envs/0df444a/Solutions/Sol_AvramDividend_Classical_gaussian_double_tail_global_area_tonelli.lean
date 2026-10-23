-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_global_area_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:13:56.20611+00:00
-- url     : https://prove2.me/submissions/45c0d7a3-6a25-4b4e-85cf-f8026844ff9b

import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_tonelli
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_full_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (μ : Measure ℝ) [SFinite μ] (φ : ℝ) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) =
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (z ^ 2 / 2) *
        ENNReal.ofReal (Real.exp (-(φ * z))) ∂μ) := by
  have hswap :
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) =
      (∫⁻ z : ℝ, ∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂volume ∂μ) := by
    simpa only [zero_mul, neg_zero, Real.exp_zero, mul_one, neg_mul] using
      (gaussian_double_tail_tonelli μ φ 0)
  have hinner (z : ℝ) :
      (∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂volume) =
      if 0 < z then ENNReal.ofReal (z ^ 2 / 2) *
        ENNReal.ofReal (Real.exp (-(φ * z))) else 0 := by
    by_cases hz : 0 < z
    · rw [if_pos hz, gaussian_double_tail_atom_full_lintegral φ z (le_of_lt hz)]
      exact mul_comm _ _
    · rw [if_neg hz]
      have hfalse : ∀ t : ℝ, ¬ (0 < t ∧ t < z) := by
        intro t ht
        exact hz (lt_trans ht.1 ht.2)
      simp [hfalse]
  calc
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) =
      (∫⁻ z : ℝ, ∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) *
            ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂volume ∂μ) := hswap
    _ = ∫⁻ z : ℝ, (if 0 < z then
        ENNReal.ofReal (z ^ 2 / 2) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ := by
      apply lintegral_congr
      intro z
      exact hinner z
    _ = ∫⁻ z in Ioi (0 : ℝ),
          ENNReal.ofReal (z ^ 2 / 2) *
            ENNReal.ofReal (Real.exp (-(φ * z))) ∂μ := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro z
      simp [Set.indicator, Set.mem_Ioi]
