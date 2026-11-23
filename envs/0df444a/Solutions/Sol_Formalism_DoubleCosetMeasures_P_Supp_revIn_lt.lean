-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Supp.revIn_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:47.783046+00:00
-- url     : https://prove2.me/submissions/9eb2ea27-cb2e-49c7-8ea3-1818e2093620

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
theorem _root_.solution : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [List.sum_cons] at h ⊢
    by_cases hj : j < a
    · simp only [revIn, hj, if_true]; omega
    · simp only [revIn, hj, if_false]
      have := solution s (j - a) (by omega); omega
end Formalism.DoubleCosetMeasures.P.Supp
