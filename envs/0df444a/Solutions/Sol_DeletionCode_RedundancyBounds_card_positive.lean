-- Prove2me | solution 1 for DeletionCode.RedundancyBounds.card_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:48:42.140051+00:00
-- url     : https://prove2.me/submissions/38e567d2-8abd-4eb4-8ef5-ab670e6e9731

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds

set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery
namespace DeletionCode.RedundancyBounds
theorem _root_.solution (n Q : ℕ) (C : Finset (Bits n))
    (hcard : 2 ^ n ≤ 8 * Q * C.card) : 0 < C.card := by
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  by_contra h
  have hz : C.card = 0 := by omega
  rw [hz, mul_zero] at hcard
  omega
end DeletionCode.RedundancyBounds
