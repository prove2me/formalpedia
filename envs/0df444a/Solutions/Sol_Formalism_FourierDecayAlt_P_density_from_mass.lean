-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.density_from_mass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:35:48.526607+00:00
-- url     : https://prove2.me/submissions/7f75ce46-7414-46c6-ab2e-6311d593a857

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrderIndexAndStrata_nn0FromMass

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.DensityFromMassFormula :=
  Formalism.FourierDecayAlt.P.OrderIndexAndStrata.nn0FromMass
end Formalism.FourierDecayAlt.P
