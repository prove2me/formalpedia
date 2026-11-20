-- Prove2me | solution 1 for DeletionCode.TaggedAnchorCount.bad_record_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:20:06.729186+00:00
-- url     : https://prove2.me/submissions/25f6f8d5-fd2a-4e99-8810-e320dc6802ea

import Definitions.Def_DeletionCode_CloseAnchorCount
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
import Definitions.Def_DeletionCode_TaggedAnchorCount
import Theorems.Thm_DeletionCode_CloseAnchorCount_bad_card_le


set_option autoImplicit true
open DeletionCode DeletionCode.TaggedAnchorCount
namespace DeletionCode.TaggedAnchorCount
theorem _root_.solution (n r m B : ℕ) :
    Nat.card {rec : Record n r // Bad m B rec} ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) * 4 ^ r := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (badEquiv n r m B),
    Fintype.card_prod, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin]
  norm_num only [Nat.reduceMul]
  apply Nat.mul_le_mul_right
  rw [Fintype.card_subtype]
  exact CloseAnchorCount.bad_card_le r n m B
end DeletionCode.TaggedAnchorCount
