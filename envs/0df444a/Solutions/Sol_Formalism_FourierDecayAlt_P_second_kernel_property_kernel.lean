-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.second_kernel_property_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:09:53.446309+00:00
-- url     : https://prove2.me/submissions/bd859d1b-703c-45fa-bc4e-67cad97d7eb5

import Definitions.Def_Formalism_HermitianCurvature_StatementA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondKernelPropertyKernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_ReversedIndexLastBlock_a2oneKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A.LevelOneKernelPair :=
  Formalism.FourierDecayAlt.P.ReversedIndexLastBlock.a2oneKernel
end Formalism.FourierDecayAlt.P
