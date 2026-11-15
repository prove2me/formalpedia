-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a234_combined_fullcell_one_sided_Taylor_discount_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:01:44.821301+00:00
-- url     : https://prove2.me/submissions/c21e122b-a425-488a-9936-a67b59278198

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (e0 e1 u v d h r z ε Q L M : ℝ)
    (he0 : 0 ≤ e0) (he0one : e0 ≤ 1)
    (hε : 0 ≤ ε) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hTaylor : max (e0 * (v - u - d*r - h/2*r^2)) 0 ≤ ε*r^2)
    (hDisc : |e1-e0| ≤ Q) (hLip : |v-u| ≤ L* |r|)
    (hh : |h| ≤ M) :
    max (e1 * (v-u) - e0 * (d*r + h/2*z^2)) 0 ≤
      ε*r^2 + Q*L* |r| + M/2* |r^2-z^2| := by
  have hExpand :
      e1*(v-u)-e0*(d*r+h/2*z^2) =
      e0*(v-u-d*r-h/2*r^2) + (e1-e0)*(v-u) +
        e0*(h/2)*(r^2-z^2) := by ring
  have hT : e0*(v-u-d*r-h/2*r^2) ≤ ε*r^2 :=
    (le_max_left _ _).trans hTaylor
  have hD : (e1-e0)*(v-u) ≤ Q*L * |r| := by
    have hab : |(e1-e0)*(v-u)| ≤ Q*(L * |r|) := by
      rw [abs_mul]
      exact mul_le_mul hDisc hLip (abs_nonneg _) hQ
    calc
      (e1-e0)*(v-u) ≤ |(e1-e0)*(v-u)| := le_abs_self _
      _ ≤ Q*(L * |r|) := hab
      _ = Q*L * |r| := by ring
  have heh : e0* |h| ≤ M := by
    calc
      e0* |h| ≤ 1* |h| :=
        mul_le_mul_of_nonneg_right he0one (abs_nonneg _)
      _ = |h| := one_mul _
      _ ≤ M := hh
  have hC : e0*(h/2)*(r^2-z^2) ≤ M/2* |r^2-z^2| := by
    calc
      e0*(h/2)*(r^2-z^2) ≤ |e0*(h/2)*(r^2-z^2)| :=
        le_abs_self _
      _ = (e0* |h|/2)* |r^2-z^2| := by
        simp only [abs_mul, abs_div, abs_of_nonneg he0, abs_of_nonneg
          (by norm_num : (0:ℝ) ≤ 2)]
        ring
      _ ≤ (M/2)* |r^2-z^2| :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right heh (by norm_num)) (abs_nonneg _)
  have hUpper : e1*(v-u)-e0*(d*r+h/2*z^2) ≤
      ε*r^2 + Q*L* |r| + M/2* |r^2-z^2| := by
    rw [hExpand]
    linarith
  apply max_le hUpper
  have hr : 0 ≤ r^2 := sq_nonneg _
  positivity
