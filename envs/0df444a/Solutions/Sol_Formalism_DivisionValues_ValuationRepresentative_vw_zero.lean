-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.vw_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:38.615931+00:00
-- url     : https://prove2.me/submissions/b3918569-79ef-42e3-8229-0a3e85ccc837

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ValuationRepresentative
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ValuationRepresentative
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by
  simp only [vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]
end Formalism.DivisionValues.ValuationRepresentative
