-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.I_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:34.94394+00:00
-- url     : https://prove2.me/submissions/8709d6dc-2a5d-4d42-9c1a-0cf3c97aeaca

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution {h a : A} (hc : Commute a h) : a * h = h * a := hc.eq
end Formalism.FourierDecayAlt.P.RuleSS
