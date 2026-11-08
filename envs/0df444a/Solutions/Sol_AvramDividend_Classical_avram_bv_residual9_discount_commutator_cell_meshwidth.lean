-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual9_discount_commutator_cell_meshwidth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:30:37.580068+00:00
-- url     : https://prove2.me/submissions/5bc369ee-3eb6-4cb1-bb97-dd675bb2b5c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The discount commutator is controlled by negative post-cell contact and meshwidth. -/
theorem solution
    (q a b δ post : ℝ)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hwidth : b - a ≤ δ) :
    (Real.exp (-(q * b)) - Real.exp (-(q * a))) * post ≤
      (q * δ) * max (-post) 0 := by
  have hmono : Real.exp (-(q * b)) ≤ Real.exp (-(q * a)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hab)]
  have hloss : Real.exp (-(q * a)) - Real.exp (-(q * b)) ≤
      q * (b - a) := by
    have h := avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz
      q a b hq ha hab
    linarith
  have hδ : q * (b - a) ≤ q * δ :=
    mul_le_mul_of_nonneg_left hwidth hq
  calc
    (Real.exp (-(q * b)) - Real.exp (-(q * a))) * post =
        (Real.exp (-(q * a)) - Real.exp (-(q * b))) * (-post) := by ring
    _ ≤ (Real.exp (-(q * a)) - Real.exp (-(q * b))) *
          max (-post) 0 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (sub_nonneg.mpr hmono)
    _ ≤ (q * (b - a)) * max (-post) 0 :=
      mul_le_mul_of_nonneg_right hloss (le_max_right _ _)
    _ ≤ (q * δ) * max (-post) 0 :=
      mul_le_mul_of_nonneg_right hδ (le_max_right _ _)
