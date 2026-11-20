-- Prove2me | solution 1 for DeletionCode.CodeExistence.labelCount_eq_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:13:27.274005+00:00
-- url     : https://prove2.me/submissions/5e652119-b4c2-4cae-92d6-365bcd2ad123

import Definitions.Def_DeletionCode_PaperProbability
import Definitions.Def_DeletionCode_FiniteDiscard
import Definitions.Def_DeletionCode_GoodWordBridge
import Definitions.Def_DeletionCode_RedundancyBounds
import Definitions.Def_DeletionCode_CodeExistence

set_option autoImplicit true
open DeletionCode DeletionCode.CodeExistence
open HeaderRecovery Windows SignedSupport CircleUniform CircleHash
open ExceptionalProbability ObstructionProbability CodeSelection
namespace DeletionCode.CodeExistence
theorem _root_.solution (t n : ℕ) :
    RedundancyBounds.labelCount t n =
      8 * ObstructionBound.scale t n (PaperParameters.k n) := by
  unfold RedundancyBounds.labelCount ObstructionBound.scale PaperParameters.L
  ring
end DeletionCode.CodeExistence
