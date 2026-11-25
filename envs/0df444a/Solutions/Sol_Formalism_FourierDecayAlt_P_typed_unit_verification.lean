-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.typed_unit_verification
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:55:46.358452+00:00
-- url     : https://prove2.me/submissions/34b9de1f-48ad-4270-9f3e-34db5d3b1123

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
theorem _root_.solution : Formalism.FourierDecayAlt.S3.TypedUnitCheck := by
  intro g r hg
  rw [← zpow_natCast (g ^ (-3 : ℤ)) (r + 1), ← _root_.zpow_mul, ← zpow_add₀ hg.ne', ← zpow_sub₀ hg.ne',
    one_div, ← _root_.zpow_neg]
  congr 1; push_cast; ring
end Formalism.FourierDecayAlt.P
