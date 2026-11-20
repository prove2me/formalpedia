-- Prove2me | solution 1 for DeletionCode.RedundancyBounds.code_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:16.661043+00:00
-- url     : https://prove2.me/submissions/ddf8d087-f2ae-4a45-b826-f033a2a8a707

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
import Theorems.Thm_DeletionCode_RedundancyBounds_card_positive

set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery
namespace DeletionCode.RedundancyBounds
theorem _root_.solution (n Q : ℕ) (C : Finset (Bits n))
    (hcard : 2 ^ n ≤ 8 * Q * C.card) : C.Nonempty :=
  Finset.card_pos.mp (card_positive n Q C hcard)
end DeletionCode.RedundancyBounds
