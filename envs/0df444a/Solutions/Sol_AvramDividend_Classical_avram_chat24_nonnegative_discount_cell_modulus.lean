-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_nonnegative_discount_cell_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:36:30.420288+00:00
-- url     : https://prove2.me/submissions/e97466b2-4310-4e8a-a152-2eecab28881f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Nonnegative discount exponentials have a one-sided Lipschitz bound. -/
theorem solution
    (q a b h : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hab : a ≤ b) (hwidth : b - a ≤ h) :
    Real.exp (-(q * a)) - Real.exp (-(q * b)) ≤ q * h := by
  have hqa : 0 ≤ q * a := mul_nonneg hq ha
  have hqb : 0 ≤ q * (b - a) :=
    mul_nonneg hq (sub_nonneg.mpr hab)
  have hEA : Real.exp (-(q * a)) ≤ 1 := by
    have hh : Real.exp (-(q * a)) ≤ Real.exp (0 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith)
    simpa using hh
  have hEB : Real.exp (-(q * (b - a))) ≤ 1 := by
    have hh : Real.exp (-(q * (b - a))) ≤ Real.exp (0 : ℝ) :=
      Real.exp_le_exp.mpr (by linarith)
    simpa using hh
  have hTaylor : 1 - Real.exp (-(q * (b - a))) ≤ q * (b - a) := by
    have hh := Real.add_one_le_exp (-(q * (b - a)))
    linarith
  have hprod : Real.exp (-(q * a)) *
      (1 - Real.exp (-(q * (b - a)))) ≤
      1 - Real.exp (-(q * (b - a))) := by
    have hh := mul_le_mul_of_nonneg_right hEA (by linarith : 0 ≤
      1 - Real.exp (-(q * (b - a))))
    nlinarith
  calc
    Real.exp (-(q * a)) - Real.exp (-(q * b)) =
        Real.exp (-(q * a)) *
          (1 - Real.exp (-(q * (b - a)))) := by
      rw [show -(q * b) = -(q * a) + -(q * (b - a)) by ring,
        Real.exp_add]
      ring
    _ ≤ 1 - Real.exp (-(q * (b - a))) := hprod
    _ ≤ q * (b - a) := hTaylor
    _ ≤ q * h := mul_le_mul_of_nonneg_left hwidth hq
