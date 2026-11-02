-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_scalar_exponential_deficit_right_slope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:52:44.696006+00:00
-- url     : https://prove2.me/submissions/5645acd6-29c3-48b0-b344-18e1ca7e8dcf

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Set

theorem solution (A : ℝ) :
    Tendsto (fun h : ℝ => h⁻¹ * (1 - Real.exp (-(h * A))))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds A) := by
  have hlin : HasDerivAt (fun h : ℝ => h * (-A)) (-A) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (-A)
  have hexp : HasDerivAt (fun h : ℝ => Real.exp (-(h * A))) (-A) 0 := by
    have hc := (Real.hasDerivAt_exp ((0 : ℝ) * (-A))).comp 0 hlin
    simpa [Function.comp_def, mul_neg, neg_mul] using hc
  have hder := (hasDerivAt_iff_tendsto_slope_zero).mp hexp
  have hsubset : (Ioi (0 : ℝ)) ⊆ {0}ᶜ := by
    intro h hh
    exact Set.mem_compl (by simpa only [Set.mem_singleton_iff] using ne_of_gt hh)
  have hlim : Tendsto
      (fun h : ℝ => h⁻¹ * (Real.exp (-(h * A)) - 1))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (-A)) := by
    simpa using hder.mono_left (nhdsWithin_mono 0 hsubset)
  convert hlim.neg using 1
  · funext h
    ring
  · ring
