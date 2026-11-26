-- Prove2me | solution 1 for Eden.radialDiscriminant_pos_on_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:24.66075+00:00
-- url     : https://prove2.me/submissions/c3bceb98-c959-4068-85fd-ac11c0cea745

import Definitions.Def_Eden_ScalarCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_Eden_RadialDynamics
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (t : ℝ) {s : ℝ}
    (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2) : 0 < radialDiscriminant t s := by
  have hu : (s - 1) ^ 2 ≤ 1 := by nlinarith
  have he := Real.exp_pos (-4 * t)
  have hm := mul_nonneg (sub_nonneg.mpr hu) (le_of_lt he)
  by_cases hz : (s - 1) ^ 2 = 0
  · simpa only [radialDiscriminant, hz, mul_zero, add_zero] using he
  · have hp : 0 < (s - 1) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    dsimp [radialDiscriminant]
    nlinarith
end Eden
