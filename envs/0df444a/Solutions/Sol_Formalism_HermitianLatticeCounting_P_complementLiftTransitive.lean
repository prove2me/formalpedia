-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.complementLiftTransitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:01.860269+00:00
-- url     : https://prove2.me/submissions/d7a3545a-0f1a-479e-a029-5d0fcebc7636

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eichlerMapIsometry
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eichlerMapFixesJointSpan
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_liftTransitive_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.LiftTransitive := liftTransitive_of eichlerMapIsometry eichlerMapFixesJointSpan
end Formalism.HermitianLatticeCounting.P
