-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.wt_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:41.374539+00:00
-- url     : https://prove2.me/submissions/78ae9536-af05-47e5-b035-85293f36d5b8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (R : ℝ) (m : ℕ) : wt R m ≤ 1 := by
  unfold wt
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_left _ _) (by norm_num)
end Formalism.MainNotions.WeightedLatticeSum
