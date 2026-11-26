-- Prove2me | solution 1 for FirstPassageLinearTransport.targetScale_rat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:44.533721+00:00
-- url     : https://prove2.me/submissions/b4f99aaa-d187-4223-b139-a528f8b1007d

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (r : ℚ) (m : ℕ) :
    targetScale (r : ℝ) m = 2 ^ rationalTargetRank r m := rfl
end FirstPassageLinearTransport
