-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:15:21.685704+00:00
-- url     : https://prove2.me/submissions/7b233c6d-668e-4c7a-a5ed-6663b6a3156a

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := HeightOneSpectrum.ext (map_cO_map_cO w.asIdeal)
end Formalism.DivisionValues.ValuationRepresentative
