-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.reductionOnto_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:57:26.004222+00:00
-- url     : https://prove2.me/submissions/5e9e9d4c-29e6-4696-ae01-f380030483d0

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_red_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.ReductionOnto := by
  intro o _ _ ι _ _
  exact red_surjective o ι
end Formalism.FourierDecayAlt.P
