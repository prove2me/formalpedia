-- Prove2me | solution 1 for AutomorphicForm.unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d1c180ed-bc41-5bff-8c2f-55f55ba2081c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace TQ4a

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

scoped instance topRing_E : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L _
scoped instance t2_E : T2Space (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.t2Space_tensor K L _
scoped instance lc_E : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.locallyCompactSpace_tensor K L _
scoped instance nontrivial_E : Nontrivial (L ⊗[K] InfiniteAdeleRing K) := (AutomorphicForm.archIdentEquiv K L).toEquiv.nontrivial

def Φ (τ : L ≃ₐ[K] L) : (L ⊗[K] InfiniteAdeleRing K) → (L ⊗[K] InfiniteAdeleRing K) :=
  fun x => Algebra.TensorProduct.map (τ : L →ₐ[K] L) (AlgHom.id K (InfiniteAdeleRing K)) x

theorem Φ_one (x : (L ⊗[K] InfiniteAdeleRing K)) : Φ K L 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp [Φ]
  | tmul l c => simp [Φ, Algebra.TensorProduct.map_tmul]
  | add x y hx hy =>
    simp only [Φ, map_add] at hx hy ⊢
    rw [hx, hy]

theorem Φ_mul (τ₁ τ₂ : L ≃ₐ[K] L) (x : (L ⊗[K] InfiniteAdeleRing K)) : Φ K L (τ₁ * τ₂) x = Φ K L τ₁ (Φ K L τ₂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [Φ]
  | tmul l c => simp [Φ, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
  | add x y hx hy =>
    simp only [Φ, map_add] at hx hy ⊢
    rw [hx, hy]

theorem sigmaTensor_eq_Φ (σ : L ≃ₐ[K] L) (x : (L ⊗[K] InfiniteAdeleRing K)) :
    AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x = Φ K L σ x := rfl

theorem sum_Φ_mem_range [IsGalois K L] (x : (L ⊗[K] InfiniteAdeleRing K)) :
    ∑ τ : L ≃ₐ[K] L, Φ K L τ x ∈
      (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).range := by
  induction x using TensorProduct.induction_on with
  | zero => simp [Φ]
  | tmul l c =>
    have h : ∑ τ : L ≃ₐ[K] L, Φ K L τ (l ⊗ₜ[K] c) = (algebraMap K L (Algebra.trace K L l)) ⊗ₜ[K] c := by
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← TensorProduct.sum_tmul, trace_eq_sum_automorphisms]
      rfl
    rw [h, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    first
      | exact ⟨Algebra.trace K L l • c, rfl⟩
      | (rw [← TensorProduct.tmul_smul]; exact ⟨Algebra.trace K L l • c, rfl⟩)
  | add x y hx hy =>
    simp only [Φ, map_add] at hx hy ⊢
    rw [Finset.sum_add_distrib]
    exact Subalgebra.add_mem _ hx hy

theorem mem_range_of_sigmaTensor_eq [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (x : (L ⊗[K] InfiniteAdeleRing K)) (hx : AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ x = x) :
    x ∈ (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).range := by
  classical
  rw [sigmaTensor_eq_Φ] at hx

  let S : Subgroup (L ≃ₐ[K] L) :=
    { carrier := {τ | Φ K L τ x = x}
      mul_mem' := fun {τ₁ τ₂} h₁ h₂ => by
        show Φ K L (τ₁ * τ₂) x = x
        rw [Φ_mul, h₂, h₁]
      one_mem' := Φ_one K L x
      inv_mem' := fun {τ} h => by
        show Φ K L τ⁻¹ x = x
        conv_lhs => rw [← h]
        rw [← Φ_mul, inv_mul_cancel, Φ_one] }
  have hall : ∀ τ : L ≃ₐ[K] L, Φ K L τ x = x := fun τ =>
    (Subgroup.zpowers_le.mpr (show σ ∈ S from hx)) (hgen τ)
  have hsum : ∑ τ : L ≃ₐ[K] L, Φ K L τ x = (Fintype.card (L ≃ₐ[K] L) : K) • x := by
    simp only [hall, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K]
  have hn : (Fintype.card (L ≃ₐ[K] L) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have : x = (Fintype.card (L ≃ₐ[K] L) : K)⁻¹ • ∑ τ : L ≃ₐ[K] L, Φ K L τ x := by
    rw [hsum, inv_smul_smul₀ hn]
  rw [this]
  exact Subalgebra.smul_mem _ (sum_Φ_mem_range K L x) _

theorem exists_units_map_includeRight_eq [IsGalois K L] (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (a : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (ha : Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom a = a) :
    ∃ p : (InfiniteAdeleRing K)ˣ, (Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) : InfiniteAdeleRing K →* L ⊗[K] InfiniteAdeleRing K)) p = a := by
  have h1 : AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (a : (L ⊗[K] InfiniteAdeleRing K)) = a := by
    have := congrArg Units.val ha
    rwa [Units.coe_map] at this
  have h2 : AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ ((a⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (a⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
    have := congrArg Units.val ((map_inv (Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom) a).trans (congrArg Inv.inv ha))
    rwa [Units.coe_map] at this
  obtain ⟨p, hp⟩ := mem_range_of_sigmaTensor_eq K L σ hgen _ h1
  obtain ⟨p', hp'⟩ := mem_range_of_sigmaTensor_eq K L σ hgen _ h2
  replace hp : Algebra.TensorProduct.includeRight p = (a : (L ⊗[K] InfiniteAdeleRing K)) := hp
  replace hp' : Algebra.TensorProduct.includeRight p' = ((a⁻¹ : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) := hp'
  have hinj : Function.Injective (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K)) :=
    FaithfulSMul.algebraMap_injective _ _
  have halg : ∀ c : InfiniteAdeleRing K,
      algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) c = Algebra.TensorProduct.includeRight c := fun c => rfl
  have hpp' : p * p' = 1 := by
    apply hinj
    rw [map_mul, map_one, halg, halg, hp, hp', Units.mul_inv]
  have hp'p : p' * p = 1 := by rw [mul_comm]; exact hpp'
  refine ⟨⟨p, p', hpp', hp'p⟩, Units.ext ?_⟩
  rw [Units.coe_map]
  exact hp

end TQ4a
p2m_reactivate "P2MW.S_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight.TQ4a"

end
p2m_reactivate "P2MW.S_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight.TQ4a"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (s : (L ⊗[K] InfiniteAdeleRing K)ˣ) :
    Units.map (↑(AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)) s = s ↔ s ∈ Set.range (Units.map ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] (L ⊗[K] InfiniteAdeleRing K)).toRingHom.toMonoidHom)) := by
  constructor
  · intro h
    have h' : Units.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ).toMonoidHom s = s := h
    obtain ⟨p, hp⟩ := TQ4a.exists_units_map_includeRight_eq K L σ hgen s h'
    exact ⟨p, by rw [← hp]; rfl⟩
  · rintro ⟨p, rfl⟩
    apply Units.ext
    show AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ ((1 : L) ⊗ₜ[K] (p : InfiniteAdeleRing K)) =
      (1 : L) ⊗ₜ[K] (p : InfiniteAdeleRing K)
    show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K (InfiniteAdeleRing K)) ((1 : L) ⊗ₜ[K] (p : InfiniteAdeleRing K)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl

end S_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight
end P2MW
export P2MW.S_AutomorphicForm_unitsMap_sigmaTensor_eq_self_iff_mem_range_unitsMap_includeRight (solution)
