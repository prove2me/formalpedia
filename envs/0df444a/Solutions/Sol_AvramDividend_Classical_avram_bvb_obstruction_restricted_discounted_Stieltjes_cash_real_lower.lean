-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_restricted_discounted_Stieltjes_cash_real_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:46:38.191099+00:00
-- url     : https://prove2.me/submissions/5c0a2bf6-469c-4243-9147-d49153e3e208

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_discounted_Stieltjes_lintegral_lower_mass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real AvramDividend.Classical
open scoped ENNReal
theorem solution (μ : Measure ℝ) (A : Set ℝ)
    (hA : Ioc (0 : ℝ) (2 / 25 : ℝ) ⊆ A)
    (hMass : μ (Ioc (0 : ℝ) (2 / 25 : ℝ)) =
      ENNReal.ofReal (2 / 25 : ℝ))
    (hFin : (∫⁻ t in A,
      ENNReal.ofReal (Real.exp (-t)) ∂μ) ≠ ⊤) :
    (2 / 25 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤
      (∫⁻ t in A,
        ENNReal.ofReal (Real.exp (-t)) ∂μ).toReal := by
  have hBase :=
    avram_bvb_obstruction_discounted_Stieltjes_lintegral_lower_mass
      μ (2 / 25 : ℝ)
  rw [hMass] at hBase
  have hSet : (∫⁻ t in Ioc (0 : ℝ) (2 / 25 : ℝ),
      ENNReal.ofReal (Real.exp (-t)) ∂μ) ≤
      (∫⁻ t in A, ENNReal.ofReal (Real.exp (-t)) ∂μ) :=
    lintegral_mono_set hA
  have hReal := ENNReal.toReal_mono hFin (le_trans hBase hSet)
  have hExp : Real.exp (-(1 / 10 : ℝ)) ≤
      Real.exp (-(2 / 25 : ℝ)) :=
    Real.exp_le_exp.mpr (by norm_num)
  have hNum : (2 / 25 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤
      (2 / 25 : ℝ) * Real.exp (-(2 / 25 : ℝ)) :=
    mul_le_mul_of_nonneg_left hExp (by norm_num)
  have hReal' : (2 / 25 : ℝ) * Real.exp (-(2 / 25 : ℝ)) ≤
      (∫⁻ t in A, ENNReal.ofReal (Real.exp (-t)) ∂μ).toReal := by
    rw [ENNReal.toReal_mul] at hReal
    rw [ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _)),
      ENNReal.toReal_ofReal (by norm_num)] at hReal
    simpa only [mul_comm] using hReal
  exact le_trans hNum hReal' 
