-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a210_original_combined_positive_largecell_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:40.492304+00:00
-- url     : https://prove2.me/submissions/3537d57b-909d-4fe0-bcfb-bbe258e6b21f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section
/-- Original combined physical Gaussian residual, one-sided upper envelope.
   No separate absolute discount difference is required. -/
theorem solution (e0 e1 u v d h r z θ y K M : ℝ)
 (he0 : 0 ≤ e0) (he0one : e0 ≤ 1)
 (he1 : 0 ≤ e1) (he1one : e1 ≤ 1)
 (hK : 0 ≤ K) (hM : 0 ≤ M)
 (hu : |u| ≤ M) (hd : |d| ≤ M) (hh : |h| ≤ M)
 (hv : v ≤ K * Real.exp (θ * y)) :
 max (e1*(v-u) - e0*(d*r + h/2*z^2)) 0 ≤
  K*Real.exp (θ*y) + M*(1 + |r| + z^2/2) := by
 have hEp : 0 ≤ K*Real.exp (θ*y) :=
   mul_nonneg hK (le_of_lt (Real.exp_pos _))
 have hEnd : e1*v ≤ K*Real.exp (θ*y) := by
   have hOne := mul_nonneg (sub_nonneg.mpr he1one) hEp
   have hVal := mul_le_mul_of_nonneg_left hv he1
   nlinarith
 have hStart : -(e1*u) ≤ M := by
   have hu0 : -u ≤ M := (neg_le_abs _).trans hu
   have ha := mul_nonneg he1 (sub_nonneg.mpr hu0)
   have hb := mul_nonneg (sub_nonneg.mpr he1one) hM
   nlinarith
 have hLinear : -(e0*d*r) ≤ M*|r| := by
   have hD : |d*r| ≤ M*|r| := by
     rw [abs_mul]
     exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
   have ha := mul_nonneg he0
     (sub_nonneg.mpr (neg_le_abs (d*r)))
   have hb := mul_nonneg he0 (sub_nonneg.mpr hD)
   have hc := mul_nonneg (sub_nonneg.mpr he0one)
     (mul_nonneg hM (abs_nonneg r))
   nlinarith
 have hQuad : -(e0*(h/2*z^2)) ≤ M*z^2/2 := by
   have hn : -h ≤ M := (neg_le_abs _).trans hh
   have hz : 0 ≤ z^2/2 := div_nonneg (sq_nonneg _) (by norm_num)
   have ha := mul_nonneg (mul_nonneg he0 hz)
     (sub_nonneg.mpr hn)
   have hb := mul_nonneg (sub_nonneg.mpr he0one)
     (mul_nonneg hM hz)
   nlinarith
 have hRhs : 0 ≤ K*Real.exp (θ*y) + M*(1 + |r| + z^2/2) := by
   have hp : 0 ≤ (1:ℝ) + |r| + z^2/2 := by positivity
   exact add_nonneg hEp (mul_nonneg hM hp)
 apply max_le
 · nlinarith [hEnd,hStart,hLinear,hQuad]
 · exact hRhs
