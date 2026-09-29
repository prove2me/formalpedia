-- Prove2me | solution 1 for EulerMascheroni.Sondow.integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-14T09:56:06.943822+00:00
-- url     : https://prove2.me/submissions/d8eba62a-98e7-4a07-bbcf-9f42f90a8cb8

import Theorems.Thm_EulerMascheroni_Sondow_finite_cutoff_identity
import Theorems.Thm_EulerMascheroni_Sondow_remainder_tendsto_zero
import Theorems.Thm_EulerMascheroni_Sondow_cutoffError_tendsto_zero
import Mathlib.Tactic

open EulerMascheroni.Sondow Filter
open scoped Topology

theorem solution (n : ℕ) (hn : 0 < n) :
    I n = ((2*n).choose n : ℝ) * Real.eulerMascheroniConstant + L n - (A n : ℝ) := by
  have hl : Tendsto (fun N => I n - remainder n N) atTop (𝓝 (I n)) := by
    simpa using tendsto_const_nhds.sub (remainder_tendsto_zero n hn)
  have hr := (((Real.tendsto_harmonic_sub_log.const_mul ((2*n).choose n : ℝ)).add_const (L n)).sub_const
    (A n : ℝ)).add (cutoffError_tendsto_zero n)
  have he : (fun N => I n - remainder n N) =ᶠ[atTop]
      (fun N => ((2*n).choose n : ℝ)*((harmonic N : ℝ)-Real.log N)+L n-(A n : ℝ)+cutoffError n N) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
    exact finite_cutoff_identity n N hn hN
  simpa using tendsto_nhds_unique hl (hr.congr' he.symm)

#print axioms solution
