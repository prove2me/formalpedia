-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_factor_lt_one_of_positive_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:22:00.20633+00:00
-- url     : https://prove2.me/submissions/bec4497e-9a18-4eee-9df5-4f5d4b45b3ad

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x < a) :
    twoSidedExitExpectation X q a x < 1 := by
  have hgap : 0 < a - x := sub_pos.mpr hxa
  have hexp : Real.exp (-(φ * (a - x))) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact neg_lt_zero.mpr (mul_pos hφ hgap)
  have hexpENN :
      ENNReal.ofReal (Real.exp (-(φ * (a - x)))) < (1 : ℝ≥0∞) :=
    ENNReal.ofReal_lt_one.mpr hexp
  have hbound :
      twoSidedExitExpectationCorrected X q a x ≤
        ENNReal.ofReal (Real.exp (-(φ * (a - x)))) :=
    corrected_exit_exp_bound_at_positive_root
      X q hq φ hφ hroot a x ha hx (le_of_lt hxa)
  rw [chat04_twoSidedExitExpectation_eq_corrected X q a x]
  exact lt_of_le_of_lt hbound hexpENN
