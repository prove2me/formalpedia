-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.rpow_neg_three_halves
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:01.274119+00:00
-- url     : https://prove2.me/submissions/7c94777a-62da-45c9-a38a-422f0cdc23d9

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
theorem _root_.solution {t : ℝ} (ht : 0 < t) : t ^ (-(3 / 2 : ℝ)) = 1 / (t * Real.sqrt t) := by
  rw [Real.rpow_neg ht.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht, Real.rpow_one,
    ← Real.sqrt_eq_rpow, one_div]
end Formalism.MainNotions.WeightedLatticeSum
