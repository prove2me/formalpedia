-- Prove2me | solution 1 for Formalism.BehrendSets.Sums.hK1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:43.06959+00:00
-- url     : https://prove2.me/submissions/2846b929-6c59-48e6-b6f6-93f688f2d9b4

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Real
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Sums
namespace Formalism.BehrendSets.Sums
theorem _root_.solution (k : ℕ) : (1 : ℝ) ≤ (k : ℝ) + 1 := by
  have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  linarith
end Formalism.BehrendSets.Sums
