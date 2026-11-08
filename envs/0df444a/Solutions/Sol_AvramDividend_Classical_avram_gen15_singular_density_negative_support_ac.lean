-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen15_singular_density_negative_support_ac
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:25:22.131471+00:00
-- url     : https://prove2.me/submissions/780eeece-8704-4ee1-82de-d616db3504b2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- The singular Levy measure has no nonnegative jumps and satisfies Condition33's AC clause. -/
theorem solution :
    (volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) (Ici (0 : ℝ)) = 0 ∧
    (volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) ≪ volume := by
  constructor
  · rw [withDensity_apply _ measurableSet_Ici]
    have hzero : Set.EqOn
        (fun z : ℝ => if z ∈ Ioo (-1 : ℝ) 0
          then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)
        (fun _ : ℝ => (0 : ℝ≥0∞)) (Ici 0) := by
      intro z hz
      have hnot : z ∉ Ioo (-1 : ℝ) 0 := by
        intro hzneg
        exact (not_lt_of_ge hz) hzneg.2
      simp [hnot]
    rw [setLIntegral_congr_fun measurableSet_Ici hzero]
    simp
  · exact withDensity_absolutelyContinuous volume _
