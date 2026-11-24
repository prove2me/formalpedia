-- Prove2me | solution 1 for Formalism.BasicNotions.Ranks.two_pow_le_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:55:36.27287+00:00
-- url     : https://prove2.me/submissions/c67ab32d-a46c-48a3-9666-81c6794783f7

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Theorems.Thm_P2M_Formalism_BasicNotions_Ranks_n_pos__21ca74dd4535
import Theorems.Thm_Formalism_HC_Frame_two_pow_dvd_ord


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
theorem _root_.solution : 2 ^ R.e ≤ R.n := Nat.le_of_dvd R.n_pos' R.toFrame.two_pow_dvd_ord
end Formalism.BasicNotions.Ranks
