-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.map_cO_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:46.256876+00:00
-- url     : https://prove2.me/submissions/b3958c64-2b0e-4565-9e3a-252fcdc358d3

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_map_cO_map_cO

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
theorem _root_.solution (I J : Ideal (𝓞 K)) : I.map (cO K) ≤ J.map (cO K) ↔ I ≤ J := by
  constructor
  · intro h
    have h2 := Ideal.map_mono (f := cO K) h
    rwa [map_cO_map_cO, map_cO_map_cO] at h2
  · intro h
    exact Ideal.map_mono (f := cO K) h
end Formalism.DivisionValues.ValuationRepresentative
