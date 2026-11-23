-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.sm_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:39.665963+00:00
-- url     : https://prove2.me/submissions/871fc8e2-d4a8-4966-bb21-93c56cf369e0

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
theorem _root_.solution (D : ℕ) {a : K} (ha : a ≠ 0) : Function.Surjective (sm D a) := by
  intro y
  refine ⟨a⁻¹ • y, ?_⟩
  simp [sm, smul_smul, ha]
end Formalism.DivisionValues.exponent_index_lattice
