-- Prove2me | solution 2 for CohnElkies.lowerWallisRegularizedPhaseMajorant_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:38.935621+00:00
-- url     : https://prove2.me/submissions/69ab9d61-12eb-4d94-b7c0-c16807664ac5

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution (u : ℝ) :
    IntegrableOn (lowerWallisRegularizedPhaseMajorant u) (Ioi 0) := by
  have h1 : IntegrableOn (fun t:ℝ => t ^ (-2:ℝ)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have h1' : IntegrableOn (fun t:ℝ => 1 / t ^ 2) (Ioi 1) := by
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have : (0:ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
    simp only
    rw [Real.rpow_neg this, Real.rpow_two, one_div]
  have h2 : IntegrableOn (fun t:ℝ => Real.exp (-t)) (Ioi 1) := by
    simpa using exp_neg_integrableOn_Ioi 1 one_pos
  have htail : IntegrableOn (lowerWallisRegularizedPhaseMajorant u) (Ioi 1) := by
    refine (h1'.add h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp [lowerWallisRegularizedPhaseMajorant, not_le.2 (show (1:ℝ) < t from ht)]
  have hhead : IntegrableOn (lowerWallisRegularizedPhaseMajorant u) (Ioc 0 1) := by
    refine ((continuous_const (y := |u| + 2)).integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      (fun t ht => ?_) measurableSet_Ioc
    simp [lowerWallisRegularizedPhaseMajorant, ht.2]
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hhead.union htail

