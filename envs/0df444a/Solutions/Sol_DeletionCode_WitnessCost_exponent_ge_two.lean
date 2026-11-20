-- Prove2me | solution 1 for DeletionCode.WitnessCost.exponent_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:56.668164+00:00
-- url     : https://prove2.me/submissions/0add8b90-dfc3-44c0-874c-ade8bddec957

import Definitions.Def_DeletionCode_CountExponent
import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_WitnessCost

set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCost
open HeaderRecovery UniqueWordParameters
namespace DeletionCode.WitnessCost
theorem _root_.solution (t : ℕ) : 2 ≤ exponent t := by
  unfold exponent
  omega
end DeletionCode.WitnessCost
