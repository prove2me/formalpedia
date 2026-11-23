-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.map_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:02.5805+00:00
-- url     : https://prove2.me/submissions/f0e833b0-393d-4089-8ff7-28fb3eb38f4f

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
variable {R K V W : Type} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution (P : V →ₗ[K] W) (hP : Function.Surjective P) (B : Submodule R V)
    (hB : Submodule.IsLattice K B) : Submodule.IsLattice K (B.map (P.restrictScalars R)) := by
  refine ⟨hB.fg.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hB.span_eq_top,
    Submodule.map_top, LinearMap.range_eq_top.mpr hP]
end Formalism.DivisionValues.exponent_index_lattice
