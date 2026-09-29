-- Prove2me | solution 1 for GaloisRep.tangentFinite_unramifiedOutside
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fce23fc8-76aa-53df-bb58-f788b8d2617f

import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_tangentFinite_of_uniform_level
import Theorems.Thm_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_tangentFinite_unramifiedOutside

set_option autoImplicit false

open IsLocalRing Module

open scoped TensorProduct

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace WtTF

theorem exists_uniform_level_of_characters
    (L' : IntermediateField ℚ ℚ̄) [NumberField L'] (p₀ : ℕ) (hp₀ : p₀.Prime)
    (S : Finset ℕ) :
    ∃ M : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ M ∧ L' ≤ M ∧
      ∀ χ : (ℚ̄ ≃ₐ[ℚ] ℚ̄) → ZMod p₀,
        (∀ σ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄, σ ∈ L'.fixingSubgroup → τ ∈ L'.fixingSubgroup → χ (σ * τ) = χ σ + χ τ) →
        (∃ L₀ : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ L₀ ∧
          ∀ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, σ ∈ L₀.fixingSubgroup → χ σ = 0) →
        (∀ q : ℕ, q.Prime → q ∉ S → ∀ P : ValuationSubring ℚ̄, P.LiesOverPrime q →
          ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ ∈ L'.fixingSubgroup → χ σ = 0) →
        ∀ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, σ ∈ M.fixingSubgroup → χ σ = 0 :=
  AlgebraicClosure.exists_uniform_level_of_characters_unramified_outside L' p₀ hp₀ S

end WtTF

section DualNumber

variable {k : Type} [Field k]

namespace DualNumber p2m_export "DualNumber" "snd_mul lift" end DualNumber
p2m_open_scoped "DualNumber" in
theorem DualNumber.mul_eq_zero_of_mem_maximalIdeal {x y : DualNumber k}
    (hx : x ∈ maximalIdeal (DualNumber k)) (hy : y ∈ maximalIdeal (DualNumber k)) : x * y = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst,
    isUnit_iff_ne_zero, not_not] at hx hy
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, hx, zero_mul, TrivSqZeroExt.fst_zero]
  · rw [TrivSqZeroExt.snd_mul, hx, hy, TrivSqZeroExt.snd_zero, zero_smul, MulOpposite.op_zero,
      zero_smul, add_zero]

p2m_open_scoped "DualNumber" in
theorem DualNumber.smul_eq_zero_of_mem_maximalIdeal {V : Type} [AddCommGroup V]
    [Module (DualNumber k) V] {m : DualNumber k} (hm : m ∈ maximalIdeal (DualNumber k)) {w : V}
    (hw : w ∈ (maximalIdeal (DualNumber k)) • (⊤ : Submodule (DualNumber k) V)) : m • w = 0 := by
  refine Submodule.smul_induction_on (p := fun w => m • w = 0) hw ?_ ?_
  · intro a ha v _
    rw [smul_smul, DualNumber.mul_eq_zero_of_mem_maximalIdeal hm ha, zero_smul]
  · intro x y hx hy
    rw [smul_add, hx, hy, add_zero]

p2m_open_scoped "DualNumber" in
theorem DualNumber.natCast_eq_zero (p : ℕ) [CharP k p] : ((p : ℕ) : DualNumber k) = 0 := by
  rw [← TrivSqZeroExt.inl_natCast, CharP.cast_eq_zero, TrivSqZeroExt.inl_zero]

end DualNumber

section ModEps

variable {A : Type} [CommRing A] [IsLocalRing A]

namespace GaloisRepAdic p2m_export "GaloisRepAdic" "IsUnramifiedAt residual ρ isAdicContinuous V" end GaloisRepAdic
namespace GaloisRepAdic
p2m_open_scoped "GaloisRepAdic" in

private theorem _root_.GaloisRepAdic.sub_mem_maximalIdeal_smul_of_residual_eq_one (ρ : GaloisRepAdic A)
    {τ : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hτ : ρ.residual.ρ τ = 1) (v : ρ.V) :
    ρ.ρ τ v - v ∈ (maximalIdeal A) • (⊤ : Submodule A ρ.V) := by
  have h1 : (1 : ResidueField A) ⊗ₜ[A] (ρ.ρ τ v - v) = (0 : ResidueField A ⊗[A] ρ.V) := by
    have := LinearMap.congr_fun hτ ((1 : ResidueField A) ⊗ₜ[A] v)
    change (ρ.ρ τ).baseChange (ResidueField A) (1 ⊗ₜ v) = 1 ⊗ₜ v at this
    rw [LinearMap.baseChange_tmul] at this
    rw [TensorProduct.tmul_sub, this, sub_self]
  have h2 : (TensorProduct.quotTensorEquivQuotSMul ρ.V (maximalIdeal A))
      ((1 : A ⧸ maximalIdeal A) ⊗ₜ[A] (ρ.ρ τ v - v)) = 0 := by
    rw [show ((1 : A ⧸ maximalIdeal A) ⊗ₜ[A] (ρ.ρ τ v - v) : (A ⧸ maximalIdeal A) ⊗[A] ρ.V) = 0
      from h1, map_zero]
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

end GaloisRepAdic
p2m_export "" "GaloisRepAdic.sub_mem_maximalIdeal_smul_of_residual_eq_one"
end ModEps

section Additive

variable {k : Type} [Field k]

namespace GaloisRepAdic
p2m_open_scoped "GaloisRepAdic" in

private theorem _root_.GaloisRepAdic.sub_one_mul_of_residual (ρ : GaloisRepAdic (DualNumber k))
    {σ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hσ : ρ.residual.ρ σ = 1) (hτ : ρ.residual.ρ τ = 1) :
    ρ.ρ (σ * τ) - 1 = (ρ.ρ σ - 1) + (ρ.ρ τ - 1) := by
  have hcomp : (ρ.ρ σ - 1) * (ρ.ρ τ - 1) = 0 := by
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, LinearMap.zero_apply]

    have hv : (ρ.ρ τ - 1) v ∈ (maximalIdeal (DualNumber k)) • (⊤ : Submodule (DualNumber k) ρ.V) := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact ρ.sub_mem_maximalIdeal_smul_of_residual_eq_one hτ v
    refine Submodule.smul_induction_on (p := fun w => (ρ.ρ σ - 1) w = 0) hv ?_ ?_
    · intro m hm w _
      rw [map_smul]
      refine DualNumber.smul_eq_zero_of_mem_maximalIdeal hm ?_
      rw [LinearMap.sub_apply, Module.End.one_apply]
      exact ρ.sub_mem_maximalIdeal_smul_of_residual_eq_one hσ w
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  have : ρ.ρ (σ * τ) = ρ.ρ σ * ρ.ρ τ := map_mul _ _ _
  rw [this]
  have hexp : ρ.ρ σ * ρ.ρ τ = 1 + (ρ.ρ σ - 1) + (ρ.ρ τ - 1) + (ρ.ρ σ - 1) * (ρ.ρ τ - 1) := by
    noncomm_ring
  rw [hexp, hcomp, add_zero]
  abel

end GaloisRepAdic
p2m_export "" "GaloisRepAdic.sub_one_mul_of_residual"
namespace GaloisRepAdic
p2m_open_scoped "GaloisRepAdic" in

private theorem _root_.GaloisRepAdic.ρ_eq_one_of_sub_mem_sq (ρ : GaloisRepAdic (DualNumber k))
    {τ : ℚ̄ ≃ₐ[ℚ] ℚ̄}
    (h : ∀ v : ρ.V, ρ.ρ τ v - v ∈ (maximalIdeal (DualNumber k) ^ 2) • (⊤ : Submodule (DualNumber k) ρ.V)) :
    ρ.ρ τ = 1 := by
  have hsq : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    rw [Ideal.mem_bot]
    exact DualNumber.mul_eq_zero_of_mem_maximalIdeal hx hy
  refine LinearMap.ext fun v => ?_
  rw [Module.End.one_apply, ← sub_eq_zero]
  have hv := h v
  rw [hsq, Submodule.bot_smul, Submodule.mem_bot] at hv
  exact hv

end GaloisRepAdic
p2m_export "" "GaloisRepAdic.ρ_eq_one_of_sub_mem_sq"
end Additive

namespace WtTFSol

open GaloisRep

variable (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]

theorem tangentFinite_unramifiedOutside [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (S : Finset ℕ) :
    TangentFinite 𝒪 ρbar
      (fun _A _ _ _ ρ => ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q) := by
  classical

  set k := ResidueField 𝒪 with hk

  have hp : (ringChar k).Prime := CharP.char_is_prime k (ringChar k)
  haveI : Fact (ringChar k).Prime := ⟨hp⟩

  obtain ⟨L, hLfin, hL⟩ := ρbar.factorsThroughFiniteLevel
  haveI : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := hLfin }

  obtain ⟨M, hMfin, hLM, hM⟩ := WtTF.exists_uniform_level_of_characters L (ringChar k) hp S
  refine tangentFinite_of_uniform_level 𝒪 ρbar _ ⟨M, hMfin, ?_⟩
  letI : Algebra 𝒪 (DualNumber k) :=
    ((algebraMap k (DualNumber k)).comp (algebraMap 𝒪 k)).toAlgebra
  letI : Algebra k (ResidueField (DualNumber k)) :=
    ((IsLocalRing.residue (DualNumber k)).comp (algebraMap k (DualNumber k))).toAlgebra
  intro ρ hunr hres σ hσM

  have hres_one : ∀ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄, τ ∈ L.fixingSubgroup → ρ.residual.ρ τ = 1 := by
    intro τ hτ
    obtain ⟨e⟩ := hres
    refine LinearMap.ext fun x => e.toLinearEquiv.injective ?_
    rw [e.map_apply, Module.End.one_apply]
    change (ρbar.ρ τ).baseChange (ResidueField (DualNumber k)) (e.toLinearEquiv x) =
      e.toLinearEquiv x
    rw [hL τ ((IntermediateField.mem_fixingSubgroup_iff L τ).mp hτ), LinearMap.baseChange_one,
      Module.End.one_apply]

  haveI : CharP k (ringChar k) := ringChar.charP k
  haveI : Module (ZMod (ringChar k)) (Module.End (DualNumber k) ρ.V) :=
    AddCommGroup.zmodModule (fun f => by
      rw [← Nat.cast_smul_eq_nsmul (DualNumber k), DualNumber.natCast_eq_zero, zero_smul])
  let b := Module.Basis.ofVectorSpace (ZMod (ringChar k)) (Module.End (DualNumber k) ρ.V)

  let χ : Module.Basis.ofVectorSpaceIndex (ZMod (ringChar k)) (Module.End (DualNumber k) ρ.V) →
      (ℚ̄ ≃ₐ[ℚ] ℚ̄) → ZMod (ringChar k) :=
    fun i τ => if τ ∈ L.fixingSubgroup then b.repr (ρ.ρ τ - 1) i else 0
  have hχ : ∀ i, χ i σ = 0 := by
    intro i
    refine hM (χ i) ?_ ?_ ?_ σ ((IntermediateField.mem_fixingSubgroup_iff M σ).mpr hσM)
    ·
      intro τ₁ τ₂ h₁ h₂
      show (if τ₁ * τ₂ ∈ L.fixingSubgroup then b.repr (ρ.ρ (τ₁ * τ₂) - 1) i else 0) =
        (if τ₁ ∈ L.fixingSubgroup then b.repr (ρ.ρ τ₁ - 1) i else 0) +
          (if τ₂ ∈ L.fixingSubgroup then b.repr (ρ.ρ τ₂ - 1) i else 0)
      rw [if_pos h₁, if_pos h₂, if_pos (L.fixingSubgroup.mul_mem h₁ h₂),
        ρ.sub_one_mul_of_residual (hres_one τ₁ h₁) (hres_one τ₂ h₂), map_add, Finsupp.add_apply]
    ·
      obtain ⟨L₀, hL₀fin, hL₀⟩ := ρ.isAdicContinuous 2
      refine ⟨L₀, hL₀fin, fun τ hτ => ?_⟩
      have h1 : ρ.ρ τ = 1 :=
        ρ.ρ_eq_one_of_sub_mem_sq (hL₀ τ ((IntermediateField.mem_fixingSubgroup_iff L₀ τ).mp hτ))
      show (if τ ∈ L.fixingSubgroup then b.repr (ρ.ρ τ - 1) i else 0) = 0
      rw [h1, sub_self, map_zero, Finsupp.zero_apply, ite_self]
    ·
      intro q hq hqS P hP τ hτ _
      have h1 : ρ.ρ τ = 1 := hunr q hq hqS P hP τ hτ
      show (if τ ∈ L.fixingSubgroup then b.repr (ρ.ρ τ - 1) i else 0) = 0
      rw [h1, sub_self, map_zero, Finsupp.zero_apply, ite_self]

  have hσL : σ ∈ L.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le hLM ((IntermediateField.mem_fixingSubgroup_iff M σ).mpr hσM)
  have hD : ρ.ρ σ - 1 = 0 := by
    refine b.ext_elem fun i => ?_
    have h := hχ i
    rw [show χ i σ = b.repr (ρ.ρ σ - 1) i from if_pos hσL] at h
    rw [h, map_zero, Finsupp.zero_apply]
  exact sub_eq_zero.mp hD

end WtTFSol

p2m_open "IsLocalRing Module.IsLocalRing GaloisRep"

theorem solution (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (S : Finset ℕ) :
    TangentFinite 𝒪 ρbar (fun _A _ _ _ ρ => ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q) :=
  WtTFSol.tangentFinite_unramifiedOutside 𝒪 ρbar S

end S_GaloisRep_tangentFinite_unramifiedOutside
end P2MW
export P2MW.S_GaloisRep_tangentFinite_unramifiedOutside (solution)
