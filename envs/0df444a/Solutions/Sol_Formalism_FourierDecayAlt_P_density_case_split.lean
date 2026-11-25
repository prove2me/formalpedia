-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.density_case_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:46:13.684266+00:00
-- url     : https://prove2.me/submissions/7eae820d-6d66-43f4-a839-36b65ffa3809

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x5
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.DensCases := by
  intro η q k r c
  refine ⟨?_, ?_, ?_⟩ <;> congr 1 <;> push_cast <;> ring
end Formalism.FourierDecayAlt.P
