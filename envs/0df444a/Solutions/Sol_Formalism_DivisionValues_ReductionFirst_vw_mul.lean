-- Prove2me | solution 1 for Formalism.DivisionValues.ReductionFirst.vw_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:35.626511+00:00
-- url     : https://prove2.me/submissions/2c5cabbe-cd28-4f06-a0ee-d963de5fb25c

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 ha)
      (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hb)]
end Formalism.DivisionValues.ReductionFirst
