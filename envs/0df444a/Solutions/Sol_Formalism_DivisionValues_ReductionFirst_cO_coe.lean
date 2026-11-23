-- Prove2me | solution 1 for Formalism.DivisionValues.ReductionFirst.cO_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:02:33.553655+00:00
-- url     : https://prove2.me/submissions/8136631b-1ef6-493a-b4a8-d2eb95440974

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ReductionFirst
theorem _root_.solution (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl
end Formalism.DivisionValues.ReductionFirst
