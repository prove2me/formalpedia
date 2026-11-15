-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a253_Gaussian_HJB_antitone_factor_gives_uniform_lower_weighted_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:51:15.819649+00:00
-- url     : https://prove2.me/submissions/3a3f4fe8-af8a-4de9-a732-6fc4c45ca9d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (lambdaPlus lambdaMinus y gAtA gAtY : ℝ)
    (hOrder : lambdaMinus ≤ lambdaPlus)
    (hy : 0 ≤ y)
    (hAnti : gAtA ≤ gAtY) :
    -|gAtA| ≤ Real.exp ((lambdaMinus-lambdaPlus)*y)*gAtY := by
  have hneg : (lambdaMinus-lambdaPlus)*y ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hOrder) hy
  have hp : 0 ≤ Real.exp ((lambdaMinus-lambdaPlus)*y) :=
    Real.exp_nonneg _
  have hu : Real.exp ((lambdaMinus-lambdaPlus)*y) ≤ 1 :=
    Real.exp_le_one_iff.mpr hneg
  have hLow : -|gAtA| ≤
      Real.exp ((lambdaMinus-lambdaPlus)*y)*gAtA := by
    by_cases h : 0 ≤ gAtA
    · have : 0 ≤ Real.exp ((lambdaMinus-lambdaPlus)*y)*gAtA :=
        mul_nonneg hp h
      have habs : 0 ≤ |gAtA| := abs_nonneg _
      linarith
    · have hlt : gAtA < 0 := lt_of_not_ge h
      have habs : |gAtA| = -gAtA := abs_of_neg hlt
      have hb := mul_le_mul_of_nonpos_right hu hlt.le
      simp only [one_mul] at hb
      rw [habs]
      linarith
  exact hLow.trans (mul_le_mul_of_nonneg_left hAnti hp)
