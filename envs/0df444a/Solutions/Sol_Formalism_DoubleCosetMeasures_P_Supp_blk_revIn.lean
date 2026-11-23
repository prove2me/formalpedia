-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.blk_revIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:52:24.358802+00:00
-- url     : https://prove2.me/submissions/59f66a32-7501-4467-bb35-ae5c8d6c498b

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_ExistsContinuousLowerUpperEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.Supp
namespace Formalism.DoubleCosetMeasures.P.Supp
theorem _root_.solution : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < a
    · have e : revIn (a :: s) j = a - 1 - j := by simp [revIn, hj]
      rw [e]
      have h1 : a - 1 - j < a := by omega
      simp only [blk, h1, hj, if_true]
    · have e : revIn (a :: s) j = a + revIn s (j - a) := by simp [revIn, hj]
      rw [e]
      have h1 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [blk, h1, hj, if_false, Nat.add_sub_cancel_left]
      rw [solution s (j - a) (by omega)]
end Formalism.DoubleCosetMeasures.P.Supp
