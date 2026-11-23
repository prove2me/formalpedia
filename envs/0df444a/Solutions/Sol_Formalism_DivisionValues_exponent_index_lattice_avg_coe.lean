-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.avg_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:34:00.137519+00:00
-- url     : https://prove2.me/submissions/3f361136-b2f1-4387-a1a4-5838d49204f9

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
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {Γ : Type} [Group Γ] [Fintype Γ] (ρ : Γ →* Module.End K V)
namespace Formalism.DivisionValues.exponent_index_lattice
theorem _root_.solution (v : V) : ((avg ρ v : invSub ρ) : V) = ((Fintype.card Γ : K)⁻¹) • ∑ δ, ρ δ v := by
  simp only [avg, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.sum_apply]
end Formalism.DivisionValues.exponent_index_lattice
