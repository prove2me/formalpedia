-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.second_kernel_property_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:55:23.023705+00:00
-- url     : https://prove2.me/submissions/059ab5f5-c109-4ccc-a0cb-c19c120dde22

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_a2one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A.LevelOneKernelPoint := Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2one
end Formalism.FourierDecayAlt.P
