-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.vw_star_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:50.820855+00:00
-- url     : https://prove2.me/submissions/4ad43e08-0b3a-4eb3-93bc-61ab127fefef

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_cO_apply
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_conjPl_conjPl
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_count_map
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_zero
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_int

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
    vw w (star (x : K)) = vw (conjPl w) (x : K) := by
  by_cases hx : x = 0
  · subst hx
    simp [vw_zero]
  · have hJ : (Ideal.span {x} : Ideal (𝓞 K)) ≠ 0 := by
      rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    have key := count_map (conjPl w) (Ideal.span {x}) hJ
    rw [conjPl_conjPl] at key
    rw [← cO_apply, vw_int, vw_int, ← key, Ideal.map_span, Set.image_singleton]
end Formalism.DivisionValues.ValuationRepresentative
