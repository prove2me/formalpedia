-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.hOf_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:12.836394+00:00
-- url     : https://prove2.me/submissions/af7aa17a-4fc8-479a-b8b8-b0204a61d682

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Theorems.Thm_Formalism_RankGapBounds_LocalQuadraticParts_units_zpow_neg_one_iff

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
theorem _root_.solution (e j l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) :
    (hOf e l hl) ^ (2 ^ j) = 1 ↔
      ((((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = 1 ∨
        (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) = -1) := by
  unfold hOf
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff,
    units_zpow_neg_one_iff]
  have hv : ((ZMod.unitOfCoprime l hl ^ (2 ^ j) : (ZMod (4 * 2 ^ e))ˣ) : ZMod (4 * 2 ^ e)) =
      (((l : ℤ) ^ (2 ^ j) : ℤ) : ZMod (4 * 2 ^ e)) := by
    simp [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime]
  constructor
  · rintro (h | h)
    · left
      rw [← hv, h, Units.val_one]
    · right
      rw [← hv, h, Units.val_neg, Units.val_one]
  · rintro (h | h)
    · left
      apply Units.ext
      rw [hv, h, Units.val_one]
    · right
      apply Units.ext
      rw [hv, h, Units.val_neg, Units.val_one]
end Formalism.RankGapBounds.LocalQuadraticParts
