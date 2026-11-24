-- Prove2me | solution 1 for Formalism.DivisionValues.exponent_index_lattice.inv_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:41.4048+00:00
-- url     : https://prove2.me/submissions/08195e14-aba1-40d0-a3b5-517dfcfb9b2d

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualLe
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Definitions.Def_Lemmata_HermitianVanishing_KeyZero
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_dual_comap
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_hstar
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_avg_coe
import Theorems.Thm_Formalism_DivisionValues_exponent_index_lattice_card_ne

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
theorem _root_.solution [FiniteDimensional K V] (pair : V →ₗ⋆[K] V →ₗ[K] K) (hs : pair.IsSymm)
    (hn : pair.Nondegenerate) (hiso : ∀ γ x y, pair (ρ γ x) (ρ γ y) = pair x y)
    (A : Submodule (𝓞 K) V) (hA : Submodule.IsLattice K A) :
    Formalism.HermitianLatticesTheory.dual (pair.domRestrict₁₂ (invSub ρ) (invSub ρ))
              (A.comap ((invSub ρ).subtype.restrictScalars (𝓞 K))) =
      (Formalism.HermitianLatticesTheory.dual pair A).map ((avg ρ).restrictScalars (𝓞 K)) := by
  refine dual_comap (R := 𝓞 K) pair hs hn (pair.domRestrict₁₂ (invSub ρ) (invSub ρ))
    ⟨fun x y => hs.eq _ _⟩ hstar (invSub ρ).subtype (avg ρ)
    ?_ (Submodule.subtype_injective _) ?_ A hA
  · intro x z
    rw [LinearMap.domRestrict₁₂_apply, avg_coe, map_smulₛₗ, LinearMap.smul_apply, map_sum,
      LinearMap.sum_apply]
    have : ∀ δ, pair (ρ δ x) (z : V) = pair x (z : V) := by
      intro δ
      conv_lhs => rw [← z.2 δ]
      exact hiso δ x z
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul, map_inv₀,
      map_natCast, Submodule.subtype_apply]
    rw [← mul_assoc, inv_mul_cancel₀ (card_ne (K := K) (Γ := Γ)), one_mul]
  · intro z
    refine ⟨z, Subtype.ext ?_⟩
    rw [avg_coe]
    have hz : ∀ δ, ρ δ (z : V) = z := z.2
    simp only [hz, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ (card_ne (K := K) (Γ := Γ)), one_smul]
end Formalism.DivisionValues.exponent_index_lattice
