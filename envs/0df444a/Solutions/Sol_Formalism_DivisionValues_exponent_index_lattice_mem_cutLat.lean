-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.mem_cutLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:02.553828+00:00
-- url     : https://prove2.me/submissions/69c525fe-1f59-49c6-9e0c-45dd1eef7caf

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
theorem _root_.solution {n d : ℕ} (E : Matrix (Fin n) (Fin d) K) (A : Submodule (𝓞 K) (Fin n → K))
    (z : Fin d → K) : z ∈ cutLat E A ↔ E.mulVec z ∈ A := Iff.rfl
end Formalism.DivisionValues.exponent_index_lattice
