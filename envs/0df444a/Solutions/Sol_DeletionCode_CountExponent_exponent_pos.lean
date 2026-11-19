-- Prove2me | solution 1 for DeletionCode.CountExponent.exponent_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:20:44.710502+00:00
-- url     : https://prove2.me/submissions/fe432a9f-b3d1-4ccc-9186-040667cf4ef5

import Definitions.Def_DeletionCode_DescriptionCount
import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_CountExponent

set_option autoImplicit true
open DeletionCode DeletionCode.CountExponent
open DescriptionCount HeaderRecovery
namespace DeletionCode.CountExponent
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) : 1 ≤ exponent t := by
  unfold exponent
  nlinarith
end DeletionCode.CountExponent
