-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.wt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:41.84391+00:00
-- url     : https://prove2.me/submissions/bcf208bc-38c4-4cda-b0b7-23ed5ccce38a

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
theorem _root_.solution (R : ℝ) (m : ℕ) : 0 ≤ wt R m := by
  unfold wt
  exact Real.rpow_nonneg (le_trans zero_le_one (le_max_left _ _)) _
end Formalism.MainNotions.WeightedLatticeSum
