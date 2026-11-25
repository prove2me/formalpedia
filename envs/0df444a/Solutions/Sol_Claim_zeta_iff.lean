-- Prove2me | solution 1 for Claim.zeta_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:09.961461+00:00
-- url     : https://prove2.me/submissions/6496f095-7f41-493a-a17a-898e46eadaab

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Claim
namespace Claim
theorem _root_.solution : Zeta ↔ RiemannHypothesis := Iff.rfl
end Claim
