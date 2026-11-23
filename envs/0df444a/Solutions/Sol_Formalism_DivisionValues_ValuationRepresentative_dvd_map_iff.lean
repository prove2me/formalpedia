-- Prove2me | solution 1 for Formalism.DivisionValues.ValuationRepresentative.dvd_map_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:30:32.917893+00:00
-- url     : https://prove2.me/submissions/758dfd71-c1fd-4e4e-aa5d-398b574990df

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_map_cO_le_iff

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) (n : ℕ) :
    (v.asIdeal.map (cO K)) ^ n ∣ J.map (cO K) ↔ v.asIdeal ^ n ∣ J := by
  rw [← Ideal.map_pow, Ideal.dvd_iff_le, Ideal.dvd_iff_le, map_cO_le_iff]
end Formalism.DivisionValues.ValuationRepresentative
