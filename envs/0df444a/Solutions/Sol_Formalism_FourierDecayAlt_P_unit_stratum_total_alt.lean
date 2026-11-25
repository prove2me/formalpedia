-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unit_stratum_total_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:49:15.748191+00:00
-- url     : https://prove2.me/submissions/eb72b799-e700-487b-a06b-f143139bf4bc

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_unitStratumTotal

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.UnitStratumTotal :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.unitStratumTotal
end Formalism.FourierDecayAlt.P
