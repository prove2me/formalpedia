-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.mass_formula_sharp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:44:24.159571+00:00
-- url     : https://prove2.me/submissions/798280c9-9cab-4a1c-82a2-d042309ba0c6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_mainSharp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.MainSharp :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.mainSharp
end Formalism.FourierDecayAlt.P
