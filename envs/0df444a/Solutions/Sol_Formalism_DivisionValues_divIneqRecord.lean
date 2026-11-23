-- Prove2me | solution 1 for Formalism.DivisionValues.divIneqRecord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:39.696154+00:00
-- url     : https://prove2.me/submissions/a966f5a7-b086-4b07-a62e-8f9145ec2a3a

import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_FinalW
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Definitions.Def_Formalism_QuotientMetricDivisors_SixthReductionExplicit
import Theorems.Thm_Formalism_DivisionValues_divisor_inequality_explicit


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
theorem _root_.solution : DivIneqRecord := divisor_inequality_explicit
end Formalism.DivisionValues
