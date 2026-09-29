-- Prove2me | solution 1 for Deformation.DieudonneModule.fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/eebad99e-97a5-5ae6-b9b4-d608b5dfc77d

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge
import Theorems.Thm_Deformation_DieudonneModule_exists_surjective_of
import Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
p2m_attr_erase "instance" "CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation
p2m_export "Deformation" "HondaSystem wittHomMap coe_wittHomMap wittHomShiftLE DieudonneModule DieudonneModule.map WittGhost.ghostComponent_map fontaineHodge of_mem_fontaineHodge of_mem_fontaineHodge_iff map_fontaineHodge_le SpecialFibre.reduction_surjective SpecialFibre.ker_reduction_eq_span DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge DieudonneModule.exists_surjective_of"
namespace FontaineExactL
p2m_open "Deformation"

section Abstract

variable {M M₁ : Type*} [AddCommGroup M] [AddCommGroup M₁]

theorem forall_exists_mem_map_eq (q : ℕ) (f : M →+ M₁) (F : M → M) (F₁ : M₁ → M₁)
    (hfF : ∀ z, f (F z) = F₁ (f z)) (L : Submodule ℤ M) (L₁ : Submodule ℤ M₁)
    (hfL : ∀ z ∈ L, f z ∈ L₁) (hsh2 : ∀ z : M, ∃ m, ∃ l ∈ L, z = F m + l)
    (hsh1 : ∀ x ∈ L₁, (∃ m, F₁ m = x) → ∃ y ∈ L₁, x = q • y)
    (hf : ∀ z₁ ∈ L₁, ∃ z, f z = z₁) (N : ℕ) (hN : ∀ z₁ : M₁, q ^ N • z₁ = 0) :
    ∀ z₁ ∈ L₁, ∃ z ∈ L, f z = z₁ := by

  have step : ∀ z₁ ∈ L₁, ∃ z ∈ L, ∃ y ∈ L₁, z₁ = f z + q • y := by
    intro z₁ hz₁
    obtain ⟨z, rfl⟩ := hf z₁ hz₁
    obtain ⟨m, l, hl, rfl⟩ := hsh2 z
    have hmem : f (F m + l) - f l ∈ L₁ := L₁.sub_mem hz₁ (hfL l hl)
    have hrange : ∃ m₁, F₁ m₁ = f (F m + l) - f l :=
      ⟨f m, by rw [map_add, hfF, add_sub_cancel_right]⟩
    obtain ⟨y, hy, hy'⟩ := hsh1 _ hmem hrange
    exact ⟨l, hl, y, hy, by rw [← hy', add_sub_cancel]⟩

  have iter : ∀ n : ℕ, ∀ z₁ ∈ L₁, ∃ z ∈ L, ∃ y ∈ L₁, z₁ = f z + q ^ n • y := by
    intro n
    induction n with
    | zero =>
      intro z₁ hz₁
      exact ⟨0, L.zero_mem, z₁, hz₁, by rw [map_zero, pow_zero, one_smul, zero_add]⟩
    | succ n ih =>
      intro z₁ hz₁
      obtain ⟨z, hz, y, hy, rfl⟩ := ih z₁ hz₁
      obtain ⟨z', hz', y', hy', rfl⟩ := step y hy
      refine ⟨z + q ^ n • z', L.add_mem hz (nsmul_mem hz' _), y', hy', ?_⟩
      rw [map_add, map_nsmul, smul_add, smul_smul, ← pow_succ, add_assoc]
  intro z₁ hz₁
  obtain ⟨z, hz, y, hy, rfl⟩ := iter N z₁ hz₁
  exact ⟨z, hz, by rw [hN, add_zero]⟩

end Abstract

section Unipotent

open WithConv

variable {k : Type u} [Field k] {B : Type v} [CommRing B] [Bialgebra k B] [Coalgebra.IsCocomm k B]

theorem mem_maximalIdeal_of_apply_one_eq_zero
    (hloc : IsLocalRing (CartierDual k B)) (φ : CartierDual k B) (hφ : φ 1 = 0) :
    φ ∈ IsLocalRing.maximalIdeal (CartierDual k B) := by
  haveI := hloc
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨ψ', hψ'⟩ := hu.exists_right_inv
  have h1 := congrArg (fun χ : CartierDual k B => χ 1) hψ'
  rw [CartierDual.mul_apply, Bialgebra.comul_one, Algebra.TensorProduct.one_def,
    TensorProduct.dualDistrib_apply, CartierDual.one_apply, Bialgebra.counit_one,
    CartierDual.toDual_apply, hφ, zero_mul] at h1
  exact zero_ne_one h1

theorem toConv_toDual_pow (φ : CartierDual k B) :
    ∀ m : ℕ, toConv (CartierDual.toDual k B (φ ^ m)) = (toConv (CartierDual.toDual k B φ)) ^ m
  | 0 => by
    rw [pow_zero, pow_zero]
    apply WithConv.ext
    rw [ofConv_toConv, CartierDual.convOne_ofConv_eq_counit]
    rfl
  | m + 1 => by
    rw [pow_succ, pow_succ, ← toConv_toDual_pow φ m, CartierDual.toDual_mul, toConv_ofConv]

variable [Module.Finite k B]

theorem isNilpotent_maximalIdeal (hloc : IsLocalRing (CartierDual k B)) :
    IsNilpotent (IsLocalRing.maximalIdeal (CartierDual k B)) := by
  haveI := hloc
  haveI : IsArtinianRing (CartierDual k B) := IsArtinianRing.of_finite k (CartierDual k B)
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := CartierDual k B)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

theorem exists_forall_convPow_eq_zero (p : ℕ) [Fact p.Prime] (hloc : IsLocalRing (CartierDual k B)) :
    ∃ N : ℕ, ∀ β : WithConv (B →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ N = 0 := by
  haveI := hloc
  obtain ⟨N, hN⟩ := isNilpotent_maximalIdeal (k := k) (B := B) hloc
  refine ⟨N, fun β hβ => ?_⟩
  set φ : CartierDual k B := CartierDual.ofDual k B β.ofConv with hφdef
  have hφ : φ ∈ IsLocalRing.maximalIdeal (CartierDual k B) :=
    mem_maximalIdeal_of_apply_one_eq_zero hloc φ hβ
  have hφN : φ ^ N = 0 := by
    have : φ ^ N ∈ IsLocalRing.maximalIdeal (CartierDual k B) ^ N := Ideal.pow_mem_pow hφ N
    rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hφpN : φ ^ p ^ N = 0 := by
    have hle : N ≤ p ^ N := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
    rw [hc, pow_add, hφN, zero_mul]
  have hβφ : β = toConv (CartierDual.toDual k B φ) := by
    rw [hφdef, CartierDual.toDual_ofDual, toConv_ofConv]
  rw [hβφ, ← toConv_toDual_pow, hφpN, map_zero]
  rfl

end Unipotent

section RightExactM

p2m_open "Deformation.DieudonneModule"

variable (k : Type u) [Field k] [PerfectField k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]

theorem map_surjective_of_isLocalRing
    {B : Type v} [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    {Q : Type w} [CommRing Q] [Bialgebra k Q] (π : B →ₐc[k] Q) (hπ : Surjective π)
    (hB : IsLocalRing (CartierDual k B)) : Surjective (DieudonneModule.map k p π) := by
  obtain ⟨N, hN⟩ := exists_forall_convPow_eq_zero (k := k) (B := B) p hB
  intro z
  obtain ⟨m, y, rfl⟩ := exists_of z
  have hV : ∀ β : WithConv (B →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ (N + (m + 1)) = 0 := fun β hβ => by
    rw [pow_add, pow_mul, hN β hβ, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
  haveI : NeZero (N + (m + 1)) := ⟨Nat.succ_ne_zero _⟩
  have hmL : m ≤ N + (m + 1) := by omega
  obtain ⟨x, hx⟩ :=
    HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero k p (N + (m + 1)) B Q π
      hπ hV (wittHomShiftLE k p Q hmL y)
  exact ⟨of k p B (N + (m + 1)) x, by rw [map_of, hx, of_shiftLE]⟩

end RightExactM

section Purity

variable {𝓞 : Type u} [CommRing 𝓞]

theorem natCast_mem_nonZeroDivisors {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    (ℛ : Type v) [CommRing ℛ] [Algebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ] :
    (p : ℛ) ∈ nonZeroDivisors ℛ := by
  have hreg : IsSMulRegular ℛ (p : 𝓞) := Module.Flat.isSMulRegular_of_nonZeroDivisors hp
  refine mem_nonZeroDivisors_iff_right.2 fun r hr => hreg ?_
  change (p : 𝓞) • r = (p : 𝓞) • (0 : ℛ)
  rw [smul_zero, Algebra.smul_def, map_natCast, mul_comm, hr]

variable {ℛ : Type v} [CommRing ℛ] [Bialgebra 𝓞 ℛ] {ℛ₁ : Type w} [CommRing ℛ₁] [Bialgebra 𝓞 ℛ₁]

theorem mem_hopfKer_of_smul_mem [Module.Flat 𝓞 (ℛ ⊗[𝓞] ℛ₁)] (π : ℛ →ₐc[𝓞] ℛ₁) {a : 𝓞}
    (ha : a ∈ nonZeroDivisors 𝓞) {r : ℛ} (h : a • r ∈ HopfAlgebra.hopfKer π) :
    r ∈ HopfAlgebra.hopfKer π := by
  rw [HopfAlgebra.mem_hopfKer_iff] at h ⊢
  have hreg : IsSMulRegular (ℛ ⊗[𝓞] ℛ₁) a := Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  apply hreg
  change a • HopfAlgebra.coaction π r = a • (r ⊗ₜ[𝓞] (1 : ℛ₁))
  rw [← map_smul, h, TensorProduct.smul_tmul']

theorem exists_eq_of_natCast_pow_mul_mem [Module.Flat 𝓞 (ℛ ⊗[𝓞] ℛ₁)] (π : ℛ →ₐc[𝓞] ℛ₁) {p : ℕ}
    (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (n : ℕ) {r : ℛ}
    (h : (p : ℛ) ^ n * r ∈ HopfAlgebra.hopfKer π) : r ∈ HopfAlgebra.hopfKer π := by
  have hpn : ((p : 𝓞) ^ n) ∈ nonZeroDivisors 𝓞 := pow_mem hp n
  refine mem_hopfKer_of_smul_mem π hpn ?_
  rwa [Algebra.smul_def, map_pow, map_natCast]

end Purity

section PartTwo

p2m_open "Deformation.DieudonneModule Deformation.TruncWitt"

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]

theorem exists_mem_fontaineHodge_map_eq_of_mem
    (hpO : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    (ℛ₁ : Type w) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] [Module.Flat 𝓞 ℛ₁]
    (π : ℛ →ₐc[𝓞] ℛ₁) [Module.Flat 𝓞 ↥(HopfAlgebra.hopfKer π)]
    (y : DieudonneModule k p (k ⊗[𝓞] ℛ))
    (hy : y ∈ fontaineHodge k p
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom)
    (x : DieudonneModule k p (k ⊗[𝓞] ↥(HopfAlgebra.hopfKer π)))
    (hx : DieudonneModule.map k p
      (Bialgebra.TensorProduct.map (BialgHom.id k k) (HopfAlgebra.hopfKerVal π)) x = y) :
    x ∈ fontaineHodge k p
      (Algebra.TensorProduct.includeRight :
        ↥(HopfAlgebra.hopfKer π) →ₐ[𝓞] k ⊗[𝓞] ↥(HopfAlgebra.hopfKer π)).toRingHom := by

  set ℛ₂ : Subalgebra 𝓞 ℛ := HopfAlgebra.hopfKer π with hℛ₂
  set ι : ↥ℛ₂ →ₐc[𝓞] ℛ := HopfAlgebra.hopfKerVal π with hι
  set ιk := Bialgebra.TensorProduct.map (BialgHom.id k k) ι with hιk
  set red : ℛ →+* k ⊗[𝓞] ℛ :=
    (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom with hred
  set red₂ : ↥ℛ₂ →+* k ⊗[𝓞] ↥ℛ₂ :=
    (Algebra.TensorProduct.includeRight : ↥ℛ₂ →ₐ[𝓞] k ⊗[𝓞] ↥ℛ₂).toRingHom with hred₂

  have hpℛ : (p : ℛ) ∈ nonZeroDivisors ℛ := natCast_mem_nonZeroDivisors hpO ℛ
  have hkerred : RingHom.ker red ≤ Ideal.span {(p : ℛ)} :=
    (SpecialFibre.ker_reduction_eq_span (ℛ := ℛ) hk hker).le
  have hredsurj : Surjective red := SpecialFibre.reduction_surjective hk
  have hred₂surj : Surjective red₂ := SpecialFibre.reduction_surjective hk

  subst hx
  obtain ⟨n, x₂, rfl⟩ := exists_of x
  rw [map_of, of_mem_fontaineHodge_iff hpℛ hkerred hredsurj] at hy

  obtain ⟨X₂, hX₂⟩ := exists_truncate_map_eq (p := p) (n := n) hred₂surj
    (x₂ : TruncatedWittVector p n (k ⊗[𝓞] ↥ℛ₂))

  have hsq : ∀ s : ↥ℛ₂, red ((ι : ↥ℛ₂ →ₐ[𝓞] ℛ).toRingHom s) = (ιk : _ →ₐ[k] _).toRingHom (red₂ s) := by
    intro s
    simp only [hred, hred₂, hιk, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, BialgHom.coe_toAlgHom,
      Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]
  have hmaps : WittVector.map red (WittVector.map (ι : ↥ℛ₂ →ₐ[𝓞] ℛ).toRingHom X₂) =
      WittVector.map (ιk : _ →ₐ[k] _).toRingHom (WittVector.map red₂ X₂) := by
    ext i
    simp only [WittVector.map_coeff]
    exact hsq (X₂.coeff i)
  have hlift : WittVector.truncate n (WittVector.map red
      (WittVector.map (ι : ↥ℛ₂ →ₐ[𝓞] ℛ).toRingHom X₂)) =
      (wittHomMap p n ιk x₂ : TruncatedWittVector p n (k ⊗[𝓞] ℛ)) := by
    rw [coe_wittHomMap, ← hX₂, map_truncate, hmaps]
  have hghost : WittVector.ghostComponent (n - 1)
      (WittVector.map (ι : ↥ℛ₂ →ₐ[𝓞] ℛ).toRingHom X₂) ∈ Ideal.span {(p : ℛ) ^ n} := by
    rw [← truncate_map_mem_fontaineKer_iff hkerred, hlift]
    exact hy
  rw [WittGhost.ghostComponent_map, Ideal.mem_span_singleton] at hghost
  obtain ⟨c, hc⟩ := hghost

  have hcmem : (p : ℛ) ^ n * c ∈ HopfAlgebra.hopfKer π := by
    rw [← hc]
    exact (WittVector.ghostComponent (n - 1) X₂).2
  have hc₂ : c ∈ HopfAlgebra.hopfKer π := exists_eq_of_natCast_pow_mul_mem π hpO n hcmem

  have hghost₂ : WittVector.ghostComponent (n - 1) X₂ ∈ Ideal.span {((p : ↥ℛ₂)) ^ n} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨c, hc₂⟩, Subtype.ext ?_⟩
    calc ((WittVector.ghostComponent (n - 1) X₂ : ↥ℛ₂) : ℛ) = (p : ℛ) ^ n * c := hc
      _ = (((p : ↥ℛ₂) ^ n * ⟨c, hc₂⟩ : ↥ℛ₂) : ℛ) := by
        rw [Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]
  exact of_mem_fontaineHodge ⟨X₂, hX₂, hghost₂⟩

end PartTwo

section HondaAxioms

p2m_open "Deformation.DieudonneModule"

variable {R : Type u} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
variable {A : Type v} [CommRing A] [Bialgebra R A]

theorem exists_frobenius_add_of_hondaSystem
    (H : HondaSystem (p : ℤ) (DieudonneModule R p A))
    (hH : H.toDieudonneDatum = dieudonneDatum R p A) (z : DieudonneModule R p A) :
    ∃ m, ∃ l ∈ H.L, z = frobenius R p A m + l := by
  have hz : z ∈ LinearMap.range H.F ⊔ H.L := H.sh2'.symm ▸ Submodule.mem_top
  obtain ⟨_, ⟨m, rfl⟩, l, hl, rfl⟩ := Submodule.mem_sup.1 hz
  refine ⟨m, l, hl, ?_⟩
  rw [hH]
  rfl

theorem exists_eq_nsmul_of_hondaSystem
    (H : HondaSystem (p : ℤ) (DieudonneModule R p A))
    (hH : H.toDieudonneDatum = dieudonneDatum R p A) {x : DieudonneModule R p A} (hx : x ∈ H.L)
    (hxF : ∃ m, frobenius R p A m = x) : ∃ y ∈ H.L, x = p • y := by
  obtain ⟨m, rfl⟩ := hxF
  have hrange : frobenius R p A m ∈ LinearMap.range H.F := ⟨m, by rw [hH]; rfl⟩
  obtain ⟨y, hy, hxy⟩ := H.sh1_le _ hx hrange
  exact ⟨y, hy, by rw [hxy, Nat.cast_smul_eq_nsmul]⟩

end HondaAxioms

section PartOne

p2m_open "Deformation.DieudonneModule"

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]
variable {k : Type v} [Field k] [CharP k p] [Algebra 𝓞 k]

theorem baseChange_surjective {ℛ : Type w} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
    {ℛ₁ : Type w} [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Surjective π) :
    Surjective (Bialgebra.TensorProduct.map (BialgHom.id k k) π) := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a r =>
    obtain ⟨s, rfl⟩ := hπ r
    exact ⟨a ⊗ₜ[𝓞] s, by rw [Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ _ _⟩

theorem includeRight_comp_eq {ℛ : Type w} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
    {ℛ₁ : Type w} [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] (π : ℛ →ₐc[𝓞] ℛ₁) :
    (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] k ⊗[𝓞] ℛ₁).toRingHom.comp
      (π : ℛ →ₐ[𝓞] ℛ₁).toRingHom =
      (Bialgebra.TensorProduct.map (BialgHom.id k k) π : k ⊗[𝓞] ℛ →ₐ[k] k ⊗[𝓞] ℛ₁).toRingHom.comp
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom := by
  ext r
  simp only [RingHom.coe_comp, comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply, BialgHom.coe_toAlgHom,
    Bialgebra.TensorProduct.map_tmul, BialgHom.id_apply]

theorem map_mem_fontaineHodge {ℛ : Type w} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
    {ℛ₁ : Type w} [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] (π : ℛ →ₐc[𝓞] ℛ₁)
    {z : DieudonneModule k p (k ⊗[𝓞] ℛ)}
    (hz : z ∈ fontaineHodge k p (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom) :
    DieudonneModule.map k p (Bialgebra.TensorProduct.map (BialgHom.id k k) π) z ∈
      fontaineHodge k p (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] k ⊗[𝓞] ℛ₁).toRingHom :=
  map_fontaineHodge_le (R := k) (p := p)
    (π := (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] k ⊗[𝓞] ℛ₁).toRingHom)
    (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom
    (π : ℛ →ₐ[𝓞] ℛ₁).toRingHom (Bialgebra.TensorProduct.map (BialgHom.id k k) π)
    (includeRight_comp_eq (k := k) π) ⟨z, hz, rfl⟩

variable [PerfectRing k p]

theorem map_baseChange_surjective {ℛ : Type w} [CommRing ℛ] [HopfAlgebra 𝓞 ℛ]
    [Coalgebra.IsCocomm 𝓞 ℛ] [Module.Finite 𝓞 ℛ]
    {ℛ₁ : Type w} [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Surjective π)
    (hunip : IsLocalRing (CartierDual k (k ⊗[𝓞] ℛ))) :
    Surjective (DieudonneModule.map k p (Bialgebra.TensorProduct.map (BialgHom.id k k) π)) := by
  haveI : PerfectField k := PerfectRing.toPerfectField k p
  exact map_surjective_of_isLocalRing k p _ (baseChange_surjective (k := k) π hπ) hunip

theorem exists_forall_pow_nsmul_eq_zero (ℛ₁ : Type w) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁]
    [Coalgebra.IsCocomm 𝓞 ℛ₁] [Module.Finite 𝓞 ℛ₁] :
    ∃ N : ℕ, ∀ z₁ : DieudonneModule k p (k ⊗[𝓞] ℛ₁), p ^ N • z₁ = 0 := by
  obtain ⟨N, hN⟩ := Deformation.DieudonneModule.exists_surjective_of k p (k ⊗[𝓞] ℛ₁)
  refine ⟨N, fun z₁ => ?_⟩
  obtain ⟨x, rfl⟩ := hN z₁
  exact pow_nsmul_of x

theorem forall_exists_mem_fontaineHodge_map_eq
    (hpO : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (hk : Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual k (k ⊗[𝓞] ℛ)))
    (ℛ₁ : Type w) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] [Coalgebra.IsCocomm 𝓞 ℛ₁]
    [Module.Free 𝓞 ℛ₁] [Module.Finite 𝓞 ℛ₁] (hrank₁ : ∃ a : ℕ, Module.finrank 𝓞 ℛ₁ = p ^ a)
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Surjective π) :
    ∀ z ∈ fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] k ⊗[𝓞] ℛ₁).toRingHom,
      ∃ y ∈ fontaineHodge k p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] k ⊗[𝓞] ℛ).toRingHom,
        DieudonneModule.map k p
          (Bialgebra.TensorProduct.map (BialgHom.id k k) π) y = z := by

  obtain ⟨H, hH, hHL⟩ :=
    Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge p hpO hk hker ℛ hrank
  obtain ⟨H₁, hH₁, hH₁L⟩ :=
    Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge p hpO hk hker ℛ₁ hrank₁

  obtain ⟨N, hN⟩ := exists_forall_pow_nsmul_eq_zero (𝓞 := 𝓞) (k := k) p ℛ₁

  have key := forall_exists_mem_map_eq p
    (DieudonneModule.map k p (Bialgebra.TensorProduct.map (BialgHom.id k k) π))
    (frobenius k p (k ⊗[𝓞] ℛ)) (frobenius k p (k ⊗[𝓞] ℛ₁))
    (map_frobenius (Bialgebra.TensorProduct.map (BialgHom.id k k) π)) H.L H₁.L
    (fun z hz => by
      rw [hHL] at hz
      rw [hH₁L]
      exact map_mem_fontaineHodge p π hz)
    (exists_frobenius_add_of_hondaSystem p H hH)
    (fun x hx hxF => exists_eq_nsmul_of_hondaSystem p H₁ hH₁ hx hxF)
    (fun z₁ _ => map_baseChange_surjective p π hπ hunip z₁) N hN
  rw [hHL, hH₁L] at key
  exact key

end PartOne

end Deformation.FontaineExactL

set_option maxHeartbeats 3200000 in

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    (ℛ : Type v) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) ℛ)))
    (ℛ₁ : Type v) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] [Coalgebra.IsCocomm 𝓞 ℛ₁]
    [Module.Free 𝓞 ℛ₁] [Module.Finite 𝓞 ℛ₁] (hrank₁ : ∃ a : ℕ, Module.finrank 𝓞 ℛ₁ = p ^ a)
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Function.Surjective π)
    [Module.Flat 𝓞 ↥(HopfAlgebra.hopfKer π)] :
    (∀ z ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ₁).toRingHom,
      ∃ y ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) π) y = z) ∧
    (∀ y ∈ Deformation.fontaineHodge (ZMod p) p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ℛ).toRingHom,
      (∃ x, Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)) x = y) →
      ∃ x ∈ Deformation.fontaineHodge (ZMod p) p
          (Algebra.TensorProduct.includeRight :
            ↥(HopfAlgebra.hopfKer π) →ₐ[𝓞] TensorProduct 𝓞 (ZMod p) ↥(HopfAlgebra.hopfKer π)).toRingHom,
        Deformation.DieudonneModule.map (ZMod p) p
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (HopfAlgebra.hopfKerVal π)) x = y) := by
  refine ⟨Deformation.FontaineExactL.forall_exists_mem_fontaineHodge_map_eq p hp
      (ZMod.ringHom_surjective _) hker ℛ hrank hunip ℛ₁ hrank₁ π hπ, ?_⟩
  rintro y hy ⟨x, hx⟩
  exact ⟨x, Deformation.FontaineExactL.exists_mem_fontaineHodge_map_eq_of_mem p hp
    (ZMod.ringHom_surjective _) hker ℛ ℛ₁ π y hy x hx, hx⟩

end S_Deformation_DieudonneModule_fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective
end P2MW
export P2MW.S_Deformation_DieudonneModule_fontaineHodge_map_surjective_and_exists_of_mem_range_of_surjective (solution)
