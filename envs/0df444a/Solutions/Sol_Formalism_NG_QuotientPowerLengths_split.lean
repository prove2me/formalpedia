-- Prove2me | solution 1 for Formalism.NG.QuotientPowerLengths.split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:40.217541+00:00
-- url     : https://prove2.me/submissions/ae9e6914-07bb-441c-818a-b1db3d8de862

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthQuotSmulRangeFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.QuotientPowerLengths
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {V : Type*} [AddCommGroup V] [Module (FractionRing O) V] [Module O V]
  [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
namespace Formalism.NG.QuotientPowerLengths
theorem _root_.solution {M P : Type*} [AddCommGroup M] [Module O M] [AddCommGroup P] [Module O P]
    (A B : Submodule O M) (hAB : A ≤ B) (i : P →ₗ[O] M) (C : Submodule O P)
    (hiB : ∀ p, i p ∈ B) (hC : C ≤ A.comap i) (hB : B ≤ A ⊔ LinearMap.range i) :
    Module.length O (M ⧸ A) ≤ Module.length O (M ⧸ B) + Module.length O (P ⧸ C) := by
  let q : (M ⧸ A) →ₗ[O] (M ⧸ B) := Submodule.factor hAB
  have hqs : Function.Surjective q := Submodule.factor_surjective hAB
  have hC' : C ≤ LinearMap.ker (A.mkQ ∘ₗ i) := by
    intro p hp
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hC hp
  let φ : (P ⧸ C) →ₗ[O] (M ⧸ A) := C.liftQ (A.mkQ ∘ₗ i) hC'
  have hker : LinearMap.ker q ≤ LinearMap.range φ := by
    intro z hz
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective A z
    rw [LinearMap.mem_ker] at hz
    have hmB : m ∈ B := by
      have h0 : (Submodule.Quotient.mk m : M ⧸ B) = 0 := hz
      rwa [Submodule.Quotient.mk_eq_zero] at h0
    obtain ⟨a, ha, y, hy, hay⟩ := Submodule.mem_sup.mp (hB hmB)
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.mp hy
    refine ⟨Submodule.Quotient.mk p, ?_⟩
    show (Submodule.Quotient.mk (i p) : M ⧸ A) = Submodule.Quotient.mk m
    rw [Submodule.Quotient.eq]
    have he : i p - m = -a := by
      rw [← hay]
      abel
    rw [he]
    exact A.neg_mem ha
  have hex : Function.Exact (LinearMap.ker q).subtype q := by
    first
      | exact LinearMap.exact_subtype_ker_map q
      | exact fun y => ⟨fun hy => ⟨⟨y, hy⟩, rfl⟩, by rintro ⟨⟨z, hz⟩, rfl⟩; exact hz⟩
  have hlen := Module.length_eq_add_of_exact (LinearMap.ker q).subtype q
    (LinearMap.ker q).injective_subtype hqs hex
  have h1 : Module.length O (LinearMap.ker q) ≤ Module.length O (LinearMap.range φ) :=
    Module.length_le_of_injective (Submodule.inclusion hker) (Submodule.inclusion_injective hker)
  have h2 : Module.length O (LinearMap.range φ) ≤ Module.length O (P ⧸ C) :=
    Module.length_le_of_surjective φ.rangeRestrict φ.surjective_rangeRestrict
  rw [hlen, add_comm]
  exact add_le_add le_rfl (h1.trans h2)
end Formalism.NG.QuotientPowerLengths
