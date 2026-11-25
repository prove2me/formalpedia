-- Prove2me | solution 1 for Formalism.DivisionValues.goodTwist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:53:34.224734+00:00
-- url     : https://prove2.me/submissions/676587ed-0c50-4174-9df3-b211a4fd25fd

import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_FinalW
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Definitions.Def_Formalism_QuotientMetricDivisors_SixthReductionExplicit
import Theorems.Thm_Formalism_DivisionValues_good_twisted_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : GoodTwist := good_twisted_lattice
end Formalism.DivisionValues
