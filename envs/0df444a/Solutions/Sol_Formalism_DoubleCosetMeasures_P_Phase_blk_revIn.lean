-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.blk_revIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:55.004953+00:00
-- url     : https://prove2.me/submissions/27728603-76f9-4f43-ac55-0bc2c6d5797d

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, _ => by simp [blk]
  | a :: s, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < a
    · simp only [revIn, blk, if_pos hj]
      rw [if_pos (by omega)]
    · simp only [revIn, blk, if_neg hj]
      rw [if_neg (by omega)]
      have e : a + revIn s (j - a) - a = revIn s (j - a) := by omega
      rw [e, solution s (j - a) (by omega)]
end Formalism.DoubleCosetMeasures.P.Phase
