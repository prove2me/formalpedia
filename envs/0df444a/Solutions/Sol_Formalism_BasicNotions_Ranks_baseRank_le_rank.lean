-- Prove2me | solution 1 for Formalism.BasicNotions.Ranks.baseRank_le_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:22.200014+00:00
-- url     : https://prove2.me/submissions/686cb299-f8dc-4a65-ae49-091ae35b409c

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_Formalism_HC_Frame_cyclic_order_le_exponent


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
theorem _root_.solution : R.n0 ≤ R.n := R.toFrame.cyclic_order_le_exponent
end Formalism.BasicNotions.Ranks
