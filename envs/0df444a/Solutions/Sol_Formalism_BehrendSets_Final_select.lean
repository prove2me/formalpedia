-- Prove2me | solution 1 for Formalism.BehrendSets.Final.select
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:09.911094+00:00
-- url     : https://prove2.me/submissions/44ec231c-42e1-4129-b3ee-6f3aabd2d715

import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoPowDvdPowTwoPowSubOne
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoLeCastOfTwoLe
import Mathlib
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MulAbsSubLt
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select
import Definitions.Def_Formalism_BehrendSets_TranslateMean
import Theorems.Thm_Formalism_BehrendSets_select


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Final
open Formalism.BehrendSets
namespace Formalism.BehrendSets.Final
theorem _root_.solution : Select := Formalism.BehrendSets.select
end Formalism.BehrendSets.Final
