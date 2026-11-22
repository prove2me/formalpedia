-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.vw_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:01.5882+00:00
-- url     : https://prove2.me/submissions/59b737ba-7900-4d6a-ae81-7f89d0cf0d34

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    vw w (x : K) = FractionalIdeal.count K w
      ((Ideal.span {x} : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  rw [FractionalIdeal.coeIdeal_span_singleton]
  rfl
end Formalism.DivisionValues.ValuationRepresentative
