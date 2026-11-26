-- Prove2me | solution 1 for Eden.discScale_radius_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:07.677438+00:00
-- url     : https://prove2.me/submissions/aebc3cd9-0289-4680-aa52-d3095f48dba8

import Definitions.Def_Eden_InvariantSets
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Eden_AttractorDistance
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (x y : ℝ) :
    (discScale (Real.sqrt (x ^ 2 + y ^ 2)) * x) ^ 2 +
      (discScale (Real.sqrt (x ^ 2 + y ^ 2)) * y) ^ 2 ≤ 2 := by
  have hs : 0 ≤ x ^ 2 + y ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsq := Real.sq_sqrt hs
  have ha := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have han := Real.sqrt_nonneg (2 : ℝ)
  by_cases h : Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt 2
  · simp only [discScale, if_pos h, one_mul]
    nlinarith
  · have hp : 0 < Real.sqrt (x ^ 2 + y ^ 2) := by
      have := lt_of_not_ge h
      linarith
    simp only [discScale, if_neg h]
    have heq : (Real.sqrt 2 / Real.sqrt (x ^ 2 + y ^ 2) * x) ^ 2 +
        (Real.sqrt 2 / Real.sqrt (x ^ 2 + y ^ 2) * y) ^ 2 = 2 := by
      field_simp
      nlinarith [congrArg (fun z : ℝ => z * (x ^ 2 + y ^ 2)) ha]
    exact heq.le
end Eden
