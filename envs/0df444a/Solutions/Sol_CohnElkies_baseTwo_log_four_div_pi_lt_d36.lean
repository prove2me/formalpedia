-- Prove2me | solution 1 for CohnElkies.baseTwo_log_four_div_pi_lt_d36
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/0f8c920f-d950-456c-ad2e-abe2e3fe9e0f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscript_pi_gt_d40

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Finset
open CohnElkies
namespace CohnElkies
theorem _root_.solution :
    Real.log (4 / Real.pi) <
      (0.241564475270490444691036891563294425 : ℝ) := by
  have hs :
      Real.log
        (4 / (3.1415926535897932384626433832795028841971 : ℝ)) <
          (0.241564475270490444691036891563294425 : ℝ) := by
    have h := Real.log_div_le_sum_range_add
      (x := (8584073464102067615373566167204971158029 /
        71415926535897932384626433832795028841971 : ℝ))
      (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  calc
    Real.log (4 / Real.pi) <
        Real.log
          (4 / (3.1415926535897932384626433832795028841971 : ℝ)) := by
      apply Real.log_lt_log (by positivity)
      apply (div_lt_div_iff₀ Real.pi_pos
        (by norm_num :
          (0 : ℝ) < 3.1415926535897932384626433832795028841971)).2
      nlinarith [manuscript_pi_gt_d40]
    _ < (0.241564475270490444691036891563294425 : ℝ) := hs
end CohnElkies
