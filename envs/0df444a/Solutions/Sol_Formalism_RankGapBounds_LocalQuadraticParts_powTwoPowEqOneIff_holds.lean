-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.powTwoPowEqOneIff_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:14:31.054853+00:00
-- url     : https://prove2.me/submissions/80bd1c13-49b1-4903-8869-62e3dfdae0df

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_int_eq_one_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_int_eq_neg_one_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_nat_eq_one_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_zmod_nat_eq_neg_one_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_pm_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_hOf_pow_eq_one_iff
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_odd_of_coprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution : OrdersIff := by
  intro e j l hl hj
  rw [hOf_pow_eq_one_iff, zmod_int_eq_one_iff, zmod_int_eq_neg_one_iff, zmod_nat_eq_one_iff,
    zmod_nat_eq_neg_one_iff]
  push_cast
  rw [show (4 : ℤ) * 2 ^ e = 2 ^ (e + 2) by ring]
  exact pm_iff e j hj l (odd_of_coprime e l hl)
end Formalism.RankGapBounds.LocalQuadraticParts
