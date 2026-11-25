-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lead_invariant_bis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:41:33.586804+00:00
-- url     : https://prove2.me/submissions/90262eaa-62f0-4c81-b2f3-56fb0c4a20a0

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_lead_invariant

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.LeadInvariant := by
  intro A _ r L M U hL hU l hl
  exact lead_invariant hL hU l hl
end Formalism.FourierDecayAlt.P
