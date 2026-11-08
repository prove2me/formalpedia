-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_power_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:54:26.654588+00:00
-- url     : https://prove2.me/submissions/cbcd176b-b647-405f-87c1-d25668960dcf

import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_sqrt_tail_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- On geometric surplus scales the singular generator deficit grows geometrically. -/
theorem solution (k : Nat) (y : Real) (hy : 0 < y)
    (hsmall : y <= 1 / 16)
    (hpower : y <= 1 / ((2 : Real) ^ k) ^ 2) :
    (2 : Real) ^ k <=
      -(3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y) := by
  have hpowpos : 0 < (2 : Real) ^ k := pow_pos (by norm_num) _
  have hrootpos : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hpowsqpos : 0 < ((2 : Real) ^ k) ^ 2 :=
    sq_pos_of_pos hpowpos
  have hcancel :
      (1 / ((2 : Real) ^ k) ^ 2) * ((2 : Real) ^ k) ^ 2 = 1 := by
    field_simp [ne_of_gt hpowpos]
  have hscale :=
    mul_le_mul_of_nonneg_right hpower (le_of_lt hpowsqpos)
  have hcell : y * ((2 : Real) ^ k) ^ 2 <= 1 := by
    linarith
  have hsq : (Real.sqrt y * (2 : Real) ^ k) ^ 2 <= 1 := by
    calc
      _ = y * ((2 : Real) ^ k) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (le_of_lt hy)]
      _ <= 1 := hcell
  have hprod : Real.sqrt y * (2 : Real) ^ k <= 1 := by
    nlinarith [mul_nonneg (le_of_lt hrootpos) (le_of_lt hpowpos)]
  have hrec : (2 : Real) ^ k <= 1 / Real.sqrt y := by
    apply (le_div_iff₀ hrootpos).2
    nlinarith
  exact le_trans hrec
    (AvramDividend.Classical.avram_a19_singular_sqrt_tail_bound y hy hsmall)
