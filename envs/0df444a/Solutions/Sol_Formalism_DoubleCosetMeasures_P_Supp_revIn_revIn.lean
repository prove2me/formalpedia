-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.revIn_revIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:09.866834+00:00
-- url     : https://prove2.me/submissions/75251390-8019-4ed4-ae54-c0598faf4a3a

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
theorem _root_.solution : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < a
    · have e : revIn (a :: s) j = a - 1 - j := by simp [revIn, hj]
      rw [e]
      have h1 : a - 1 - j < a := by omega
      simp only [revIn, h1, if_true]; omega
    · have e : revIn (a :: s) j = a + revIn s (j - a) := by simp [revIn, hj]
      rw [e]
      have h1 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, h1, if_false, Nat.add_sub_cancel_left]
      rw [solution s (j - a) (by omega)]; omega
end Formalism.DoubleCosetMeasures.P.Supp
