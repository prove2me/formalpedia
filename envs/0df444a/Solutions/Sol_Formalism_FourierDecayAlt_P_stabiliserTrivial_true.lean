-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabiliserTrivial_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:54:12.798011+00:00
-- url     : https://prove2.me/submissions/27a9e91f-2bc4-4d8a-9cb0-793e641bdd0d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_stabiliserTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.StabiliserTrivial :=
  Formalism.FourierDecayAlt.P.S3x8.stabiliserTrivial
end Formalism.FourierDecayAlt.P
