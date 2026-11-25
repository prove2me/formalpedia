-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unipotent_levi_explicit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:51:52.524058+00:00
-- url     : https://prove2.me/submissions/c230b9f2-ac85-4087-a179-ec65b8ad5f68

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_isNU_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism.FourierDecayAlt.P.S3x1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.NUExplicit := by
  intro A _ r k x
  exact isNU_iff x
end Formalism.FourierDecayAlt.P
