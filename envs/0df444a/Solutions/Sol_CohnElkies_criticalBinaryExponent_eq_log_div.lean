-- Prove2me | solution 1 for CohnElkies.criticalBinaryExponent_eq_log_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/b5c4659c-ce65-45f9-8db6-e50ae7fdc410

import Mathlib
import Definitions.Def_SpherePacking

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
    criticalBinaryExponent =
      Real.log (2 * Real.pi / Real.exp 1) /
        (2 * Real.log 2) := by
  unfold criticalBinaryExponent Real.logb
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  field_simp
end CohnElkies
