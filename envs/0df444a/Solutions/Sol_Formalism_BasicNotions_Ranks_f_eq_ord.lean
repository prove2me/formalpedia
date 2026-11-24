-- Prove2me | solution 1 for Formalism.BasicNotions.Ranks.f_eq_ord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:41.421917+00:00
-- url     : https://prove2.me/submissions/22429c7f-3ffa-4dd9-b2eb-142509fa9587

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.HC
open Formalism Formalism.BasicNotions
open Formalism.BasicNotions.Ranks
variable (R : Ranks)
namespace Formalism.BasicNotions.Ranks
theorem _root_.solution : R.f = 2 * R.ord := rfl
end Formalism.BasicNotions.Ranks
