-- Prove2me | solution 1 for Deformation.HondaSystem.comap_L_eq_of_injective_of_map_L_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e8167842-b1fd-5ddc-be7b-5bcbdfb2c609

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Theorems.Thm_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_HondaSystem_comap_L_eq_of_injective_of_map_L_le

set_option autoImplicit false

universe u

namespace Deformation
p2m_export "Deformation" "HondaSystem"
namespace HondaSystem
p2m_export "Deformation.HondaSystem" "mk sh1_le sh2' sh1_ge L"
namespace ComapL
p2m_open "Deformation.HondaSystem Deformation"

p2m_open "Deformation P2MW.S_Deformation_HondaSystem_comap_L_eq_of_injective_of_map_L_le.Deformation"

section DVR

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
  (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})

include hℓ

private theorem irreducible_ell : Irreducible ℓ :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer ℓ).2 hℓ

private theorem ell_ne_zero : ℓ ≠ 0 := (irreducible_ell hℓ).ne_zero

omit hℓ in

private theorem mem_of_smul_mem_of_ne_zero {M : Type*} [AddCommGroup M] [Module A M]
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ})
    (L : Submodule A M) (hL : ∀ m, ℓ • m ∈ L → m ∈ L) {a : A} (ha : a ≠ 0) {m : M}
    (hm : a • m ∈ L) : m ∈ L := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha (irreducible_ell hℓ)
  have hm' : ℓ ^ n • m ∈ L := by
    have := L.smul_mem (↑u⁻¹ : A) hm
    rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  clear hm ha
  induction n generalizing m with
  | zero => simpa using hm'
  | succ n ih =>
    apply ih
    apply hL
    rwa [smul_smul, ← pow_succ']

end DVR

section Honda

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
  (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ}) {r : ℕ}
  (H : HondaSystem ℓ (Fin r → A))

include hℓ

private theorem F_injective : Function.Injective H.F := by
  intro x y hxy
  have h := congrArg H.V hxy
  rw [H.V_F_apply, H.V_F_apply] at h
  exact smul_right_injective _ (ell_ne_zero hℓ) h

private theorem mem_L_of_smul_mem (m : Fin r → A) (hm : ℓ • m ∈ H.L) : m ∈ H.L := by
  have hrange : ℓ • m ∈ LinearMap.range H.F := ⟨H.V m, H.F_V_apply m⟩
  obtain ⟨y, hy, hyy⟩ := H.sh1_le _ hm hrange
  rwa [smul_right_injective _ (ell_ne_zero hℓ) hyy]

private theorem length_quotient_range_F :
    Module.length A ((Fin r → A) ⧸ LinearMap.range H.F) = Module.finrank A ↥H.L := by
  classical

  let ψ : ↥H.L →ₗ[A] (Fin r → A) ⧸ LinearMap.range H.F := (LinearMap.range H.F).mkQ ∘ₗ H.L.subtype
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ q
    have hm : m ∈ LinearMap.range H.F ⊔ H.L := by rw [H.sh2']; exact Submodule.mem_top
    obtain ⟨f, hf, l, hl, rfl⟩ := Submodule.mem_sup.1 hm
    refine ⟨⟨l, hl⟩, ?_⟩
    change Submodule.Quotient.mk l = Submodule.Quotient.mk (f + l)
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hf, zero_add]

  have hker : ∀ x : ↥H.L, x ∈ LinearMap.ker ψ ↔ ∃ y : ↥H.L, x = ℓ • y := by
    intro x
    rw [LinearMap.mem_ker]
    change (LinearMap.range H.F).mkQ (x : Fin r → A) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := H.sh1_le _ x.2 hx
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      exact H.sh1_ge _ y.2

  let s := Module.finrank A ↥H.L
  let e : ↥H.L ≃ₗ[A] (Fin s → A) := (Module.finBasis A ↥H.L).equivFun
  let PiL : Submodule A (Fin s → A) :=
    Submodule.pi Set.univ (fun _ : Fin s => (Ideal.span {ℓ} : Submodule A A))
  have hmap : (LinearMap.ker ψ).map (e : ↥H.L →ₗ[A] (Fin s → A)) = PiL := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies, PiL]
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      obtain ⟨y, rfl⟩ := (hker x).1 hx
      rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
      exact Ideal.mem_span_singleton'.2 ⟨_, rfl⟩
    · intro hv
      choose a ha using fun i => Ideal.mem_span_singleton'.1 (hv i)
      refine ⟨ℓ • e.symm a, (hker _).2 ⟨e.symm a, rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, ha i]
  have e1 : ((Fin r → A) ⧸ LinearMap.range H.F) ≃ₗ[A] (↥H.L ⧸ LinearMap.ker ψ) :=
    (LinearMap.quotKerEquivOfSurjective ψ hψ).symm
  have e2 : (↥H.L ⧸ LinearMap.ker ψ) ≃ₗ[A] ((Fin s → A) ⧸ PiL) :=
    Submodule.Quotient.equiv _ _ e hmap
  rw [e1.length_eq, e2.length_eq, (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  change s • Ring.ord A ℓ = (s : ℕ∞)
  rw [Ring.ord_of_irreducible (irreducible_ell hℓ), nsmul_one]

end Honda

end Deformation.HondaSystem.ComapL

open Deformation.HondaSystem.ComapL in
theorem solution
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {ℓ : A}
    (hℓ : IsLocalRing.maximalIdeal A = Ideal.span {ℓ}) {r : ℕ}
    (H₁ H₂ : Deformation.HondaSystem ℓ (Fin r → A))
    (φ : (Fin r → A) →ₗ[A] (Fin r → A)) (hφ : Function.Injective φ)
    (hφF : φ ∘ₗ H₂.F = H₁.F ∘ₗ φ) (hφV : φ ∘ₗ H₂.V = H₁.V ∘ₗ φ)
    (hφL : Submodule.map φ H₂.L ≤ H₁.L) :
    Submodule.comap φ H₁.L = H₂.L := by
  have _hV := hφV
  have hF₁ : Function.Injective H₁.F := F_injective hℓ H₁
  have hF₂ : Function.Injective H₂.F := F_injective hℓ H₂

  have hrank : Module.finrank A ↥H₁.L = Module.finrank A ↥H₂.L := by
    have h := LinearMap.length_quotient_range_eq_of_injective_of_comp_eq_comp
      H₁.F H₂.F φ hF₁ hφ hφF
    rw [length_quotient_range_F hℓ H₁, length_quotient_range_F hℓ H₂] at h
    exact_mod_cast h

  have hle : H₂.L ≤ Submodule.comap φ H₁.L := Submodule.map_le_iff_le_comap.1 hφL
  refine le_antisymm ?_ hle

  have hres : ∀ x ∈ Submodule.comap φ H₁.L, φ x ∈ H₁.L := fun x hx => hx
  have h1 : Module.finrank A ↥(Submodule.comap φ H₁.L) ≤ Module.finrank A ↥H₁.L := by
    refine LinearMap.finrank_le_finrank_of_injective (f := φ.restrict hres) ?_
    intro x y hxy
    apply Subtype.ext
    apply hφ
    have := congrArg Subtype.val hxy
    simpa [LinearMap.restrict_apply] using this

  set L' := Submodule.comap φ H₁.L with hL'
  let K : Submodule A ↥L' := Submodule.comap L'.subtype H₂.L
  have hK : Module.finrank A ↥K = Module.finrank A ↥H₂.L :=
    (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hq : Module.finrank A (↥L' ⧸ K) = 0 := by
    have := Submodule.finrank_quotient_add_finrank K
    omega
  have htors : Module.IsTorsion A (↥L' ⧸ K) := Module.finrank_eq_zero_iff_isTorsion.1 hq

  intro x hx
  obtain ⟨⟨a, ha⟩, hax⟩ := @htors (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hax
  change a • x ∈ H₂.L at hax
  exact mem_of_smul_mem_of_ne_zero hℓ H₂.L (mem_L_of_smul_mem hℓ H₂)
    (nonZeroDivisors.ne_zero ha) hax

end S_Deformation_HondaSystem_comap_L_eq_of_injective_of_map_L_le
end P2MW
export P2MW.S_Deformation_HondaSystem_comap_L_eq_of_injective_of_map_L_le (solution)
