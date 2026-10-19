-- Prove2me | solution 1 for CohnElkies.exp_normalizedVolumeLog_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/eecd08bb-a2f0-4c08-87f4-121f145488da

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Nat Topology
namespace CohnElkies
theorem _root_.solution :
    Real.exp ((Real.log (2 * Real.pi) + 1) / 2) =
      Real.sqrt (2 * Real.pi * Real.exp 1) := by
  have hbase : 0 < (2 : ℝ) * Real.pi := by positivity
  have htarget : 0 ≤ (2 : ℝ) * Real.pi * Real.exp 1 := by positivity
  have hsq :
      (Real.exp ((Real.log (2 * Real.pi) + 1) / 2)) ^ 2 =
        2 * Real.pi * Real.exp 1 := by
    calc
      (Real.exp ((Real.log (2 * Real.pi) + 1) / 2)) ^ 2 =
          Real.exp
            (((Real.log (2 * Real.pi) + 1) / 2) +
              ((Real.log (2 * Real.pi) + 1) / 2)) := by
            rw [Real.exp_add]
            ring
      _ = Real.exp (Real.log (2 * Real.pi) + 1) := by
            congr 1
            ring
      _ = 2 * Real.pi * Real.exp 1 := by
            rw [Real.exp_add, Real.exp_log hbase]
  have hroot := Real.sq_sqrt htarget
  nlinarith [Real.exp_pos ((Real.log (2 * Real.pi) + 1) / 2),
    Real.sqrt_nonneg (2 * Real.pi * Real.exp 1)]
end CohnElkies
