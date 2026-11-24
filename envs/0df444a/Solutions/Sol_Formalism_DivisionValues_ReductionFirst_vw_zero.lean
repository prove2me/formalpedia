-- Prove2me | solution 1 for Formalism.DivisionValues.ReductionFirst.vw_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:10.961265+00:00
-- url     : https://prove2.me/submissions/7f76c019-b38a-4c6c-8362-e03aacc6b73d

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by
  simp [vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]
end Formalism.DivisionValues.ReductionFirst
