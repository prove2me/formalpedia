-- Prove2me | solution 1 for CohnElkies.baseTwo_log_four_div_pi_gt_d36
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/896e64cd-4590-4d61-9a25-bb09b036c211

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscript_pi_lt_d40

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
    (0.241564475270490444691036891563294424 : ℝ) <
      Real.log (4 / Real.pi) := by
  have hs :
      (0.241564475270490444691036891563294424 : ℝ) <
        Real.log
          (4 / (3.1415926535897932384626433832795028841972 : ℝ)) := by
    have h := Real.sum_range_le_log_div
      (x := (2146018366025516903843391541801242789507 /
        17853981633974483096156608458198757210493 : ℝ))
      (by norm_num) (by norm_num) 20
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  calc
    (0.241564475270490444691036891563294424 : ℝ) <
        Real.log
          (4 / (3.1415926535897932384626433832795028841972 : ℝ)) := hs
    _ < Real.log (4 / Real.pi) := by
      apply Real.log_lt_log (by positivity)
      apply (div_lt_div_iff₀
        (by norm_num :
          (0 : ℝ) < 3.1415926535897932384626433832795028841972)
        Real.pi_pos).2
      nlinarith [manuscript_pi_lt_d40]
end CohnElkies
