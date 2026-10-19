-- Prove2me | solution 2 for CohnElkies.lowerWallisPhaseTail_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:08:25.286652+00:00
-- url     : https://prove2.me/submissions/53632a0b-2493-4305-b9ec-26194f17a711

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


theorem solution :
    IntegrableOn
      (fun t : ℝ => 1 / t ^ 2 + Real.exp (-t))
      (Ioi 1) := by
  have h1 : IntegrableOn (fun t:ℝ => t ^ (-2:ℝ)) (Ioi 1) := integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  have h1' : IntegrableOn (fun t:ℝ => 1 / t ^ 2) (Ioi 1) := by
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have : (0:ℝ) ≤ t := le_of_lt (lt_trans one_pos ht)
    simp only
    rw [Real.rpow_neg this, Real.rpow_two, one_div]
  have h2 : IntegrableOn (fun t:ℝ => Real.exp (-t)) (Ioi 1) := by
    simpa using exp_neg_integrableOn_Ioi 1 one_pos
  exact h1'.add h2

