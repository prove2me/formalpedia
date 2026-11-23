-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.mem_matLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:21.353479+00:00
-- url     : https://prove2.me/submissions/4e7f0a71-8463-4b93-b6d6-6b67f275443b

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
open exponent_index_lattice RationalHermitianForm
open Formalism.DivisionValues.exponent_index_lattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution {n d : ℕ} (P : Matrix (Fin d) (Fin n) K) (A : Submodule (𝓞 K) (Fin n → K))
    (z : Fin d → K) : z ∈ matLat P A ↔ ∃ x ∈ A, P.mulVec x = z := by
  exact Iff.rfl
end Formalism.DivisionValues.exponent_index_lattice
