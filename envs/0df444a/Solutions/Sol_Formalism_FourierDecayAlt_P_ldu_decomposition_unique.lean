-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ldu_decomposition_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:48:37.603181+00:00
-- url     : https://prove2.me/submissions/8a48e2d0-230b-438b-9450-21ca0a388804

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_ldu_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.S3x7
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.LDUUnique := by
  intro A _ r L U L' U' d d' hL hU hL' hU' _ hd e
  exact ldu_unique hL hU hL' hU' hd e
end Formalism.FourierDecayAlt.P
