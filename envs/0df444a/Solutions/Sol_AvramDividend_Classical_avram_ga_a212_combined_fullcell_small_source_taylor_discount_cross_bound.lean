-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a212_combined_fullcell_small_source_taylor_discount_cross_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:48:34.085812+00:00
-- url     : https://prove2.me/submissions/5855a5e6-1477-47ef-bcfe-ad7973e685b8

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section
/-- Small original combined physical Gaussian source residual bound. -/
theorem solution (e0 e1 u v d h r z ε Q L M : ℝ)
 (he0 : 0 ≤ e0) (he0one : e0 ≤ 1)
 (hε : 0 ≤ ε) (hQ : 0 ≤ Q) (hL : 0 ≤ L) (hM : 0 ≤ M)
 (hTaylor : |v-u-d*r-h/2*r^2| ≤ ε*r^2)
 (hDisc : |e1-e0| ≤ Q)
 (hLip : |v-u| ≤ L* |r|) (hh : |h| ≤ M) :
 max (e1*(v-u)-e0*(d*r+h/2*z^2)) 0 ≤
   ε*r^2 + Q*L* |r| + M/2* |r^2-z^2| := by
 have hT : e0*(v-u-d*r-h/2*r^2) ≤ ε*r^2 := by
   calc
    e0*(v-u-d*r-h/2*r^2) ≤ e0* |v-u-d*r-h/2*r^2| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) he0
    _ ≤ e0*(ε*r^2) := mul_le_mul_of_nonneg_left hTaylor he0
    _ ≤ ε*r^2 := by
      have hp : 0 ≤ ε*r^2 := mul_nonneg hε (sq_nonneg _)
      nlinarith [mul_nonneg (sub_nonneg.mpr he0one) hp]
 have hD : (e1-e0)*(v-u) ≤ Q*L* |r| := by
   have habs : |(e1-e0)*(v-u)| ≤ Q*(L* |r|) := by
     rw [abs_mul]
     calc
       |e1-e0| * |v-u| ≤ Q* |v-u| :=
         mul_le_mul_of_nonneg_right hDisc (abs_nonneg _)
       _ ≤ Q*(L* |r|) :=
         mul_le_mul_of_nonneg_left hLip hQ
   have hraw : (e1-e0)*(v-u) ≤ |(e1-e0)*(v-u)| := le_abs_self _
   nlinarith
 have hH : e0*(h/2)*(r^2-z^2) ≤ M/2* |r^2-z^2| := by
   have hh2 : |h/2| ≤ M/2 := by
     rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
     exact div_le_div_of_nonneg_right hh (by norm_num)
   have hr0 : 0 ≤ |r^2-z^2| := abs_nonneg _
   calc
    e0*(h/2)*(r^2-z^2) ≤ |e0*(h/2)*(r^2-z^2)| :=
      le_abs_self _
    _ = e0* |h/2| * |r^2-z^2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg he0]
    _ ≤ e0*(M/2)* |r^2-z^2| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hh2 he0) hr0
    _ ≤ M/2* |r^2-z^2| := by
      have hp : 0 ≤ (M/2)* |r^2-z^2| :=
        mul_nonneg (div_nonneg hM (by norm_num)) hr0
      nlinarith [mul_nonneg (sub_nonneg.mpr he0one) hp]
 have hBound : 0 ≤ ε*r^2 + Q*L* |r| + M/2* |r^2-z^2| := by
   have h1 : 0 ≤ ε*r^2 := mul_nonneg hε (sq_nonneg _)
   have h2 : 0 ≤ Q*L* |r| :=
     mul_nonneg (mul_nonneg hQ hL) (abs_nonneg _)
   have h3 : 0 ≤ M/2* |r^2-z^2| :=
     mul_nonneg (div_nonneg hM (by norm_num)) (abs_nonneg _)
   linarith
 apply max_le
 · calc
    e1*(v-u)-e0*(d*r+h/2*z^2) =
      e0*(v-u-d*r-h/2*r^2) +
      (e1-e0)*(v-u) + e0*(h/2)*(r^2-z^2) := by ring
    _ ≤ _ := by linarith
 · exact hBound
