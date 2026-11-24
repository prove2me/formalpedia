-- Prove2me | solution 1 for Formalism.GrowthSums.Top.topCount
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:06.289107+00:00
-- url     : https://prove2.me/submissions/b9435fec-df19-49fa-b85f-7af6df75522e

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
import Theorems.Thm_Formalism_GrowthSums_top_count_holds


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
theorem _root_.solution : Formalism.GrowthSums.TopCount := Formalism.GrowthSums.top_count_holds
end Formalism.GrowthSums.Top
