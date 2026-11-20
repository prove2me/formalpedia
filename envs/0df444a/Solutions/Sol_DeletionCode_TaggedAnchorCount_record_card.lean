-- Prove2me | solution 1 for DeletionCode.TaggedAnchorCount.record_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:55.256769+00:00
-- url     : https://prove2.me/submissions/73e0e5a1-e112-4951-bc1e-9b1aad643f20

import Definitions.Def_DeletionCode_CloseAnchorCount
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
import Definitions.Def_DeletionCode_TaggedAnchorCount

set_option autoImplicit true
open DeletionCode DeletionCode.TaggedAnchorCount
namespace DeletionCode.TaggedAnchorCount
theorem _root_.solution (n r : ℕ) : Fintype.card (Record n r) = n ^ r * 4 ^ r := by
  simp only [Record, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]
end DeletionCode.TaggedAnchorCount
