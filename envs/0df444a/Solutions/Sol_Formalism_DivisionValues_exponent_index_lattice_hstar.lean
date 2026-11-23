-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.hstar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:43.956659+00:00
-- url     : https://prove2.me/submissions/de192134-8602-4c2c-82dc-293b97174f48

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open RationalHermitianForm
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K) := fun r =>
  (IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mp
    (((IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mpr ⟨r, rfl⟩).map
      (starRingEnd K).toIntAlgHom)
end Formalism.DivisionValues.exponent_index_lattice
