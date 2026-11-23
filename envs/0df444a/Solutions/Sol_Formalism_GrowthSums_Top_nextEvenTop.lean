-- Prove2me | solution 1 for Formalism.GrowthSums.Top.nextEvenTop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:21.47425+00:00
-- url     : https://prove2.me/submissions/03569acb-7cb3-4888-8385-13bf5291b346

import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Coarse
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Harmonic
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Segment
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_NextEvenTopHolds
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_LogCoef
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_Length
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_KapPrime
import Mathlib
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_LemmaATwoFactList
import Theorems.Thm_Formalism_GrowthSums_next_even_top_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GrowthSums Formalism.GrowthSums.Top
namespace Formalism.GrowthSums.Top
theorem _root_.solution : Formalism.GrowthSums.NextEvenTop := Formalism.GrowthSums.next_even_top_holds
end Formalism.GrowthSums.Top
