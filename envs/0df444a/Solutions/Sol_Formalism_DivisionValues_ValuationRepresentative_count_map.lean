-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.count_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:04.156351+00:00
-- url     : https://prove2.me/submissions/413b0878-c1b4-4753-804f-43e4da93ada0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_dvd_map_iff

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (hJ : J ≠ 0) :
    FractionalIdeal.count K (conjPl v) ((J.map (cO K) : Ideal (𝓞 K)) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
    FractionalIdeal.count K v (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
  have hJ' : J.map (cO K) ≠ 0 := fun h =>
    hJ ((Ideal.map_eq_bot_iff_of_injective (cO K).injective).mp h)
  rw [FractionalIdeal.count_coe K (conjPl v) hJ', FractionalIdeal.count_coe K v hJ]
  congr 1
  apply eq_of_forall_le_iff
  intro n
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ')
      (Associates.irreducible_mk.mpr (conjPl v).irreducible),
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
      (Associates.irreducible_mk.mpr v.irreducible),
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd]
  exact dvd_map_iff v J n
end Formalism.DivisionValues.ValuationRepresentative
