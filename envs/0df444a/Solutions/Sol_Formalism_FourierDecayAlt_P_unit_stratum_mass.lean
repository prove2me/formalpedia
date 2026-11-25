-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unit_stratum_mass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:52:09.307321+00:00
-- url     : https://prove2.me/submissions/fa566192-dcf4-4363-b912-91451c743f4d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S3.UnitStratumMass := by
  intro volNo volJH volKpp volOm cUk c J h1 h2 h3 h4 hc hJ
  subst hc; subst hJ
  refine ⟨?_, ?_, ?_⟩ <;> field_simp
end Formalism.FourierDecayAlt.P
