-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_mem_fontaineHodge_map_eq_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2ff90794-17ec-5c5c-ace3-dae1458dc399

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_Deformation_DieudonneModule_exists_hondaSystem_L_eq_fontaineHodge
import Theorems.Thm_Deformation_DieudonneModule_exists_surjective_of
import Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_map_eq_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Function
open scoped TensorProduct

universe u v w

namespace Deformation
p2m_export "Deformation" "HondaSystem wittHomShiftLE DieudonneModule DieudonneModule.map fontaineHodge map_fontaineHodge_le DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge DieudonneModule.exists_surjective_of"
namespace FontaineLSurj
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

end Deformation.FontaineLSurj

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [Field k] [CharP k p] [PerfectRing k p] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [HopfAlgebra 𝓞 ℛ] [Coalgebra.IsCocomm 𝓞 ℛ]
    [Module.Free 𝓞 ℛ] [Module.Finite 𝓞 ℛ] (hrank : ∃ a : ℕ, Module.finrank 𝓞 ℛ = p ^ a)
    (hunip : IsLocalRing (CartierDual k (TensorProduct 𝓞 k ℛ)))
    (ℛ₁ : Type w) [CommRing ℛ₁] [HopfAlgebra 𝓞 ℛ₁] [Coalgebra.IsCocomm 𝓞 ℛ₁]
    [Module.Free 𝓞 ℛ₁] [Module.Finite 𝓞 ℛ₁] (hrank₁ : ∃ a : ℕ, Module.finrank 𝓞 ℛ₁ = p ^ a)
    (π : ℛ →ₐc[𝓞] ℛ₁) (hπ : Function.Surjective π)
    (z : Deformation.DieudonneModule k p (TensorProduct 𝓞 k ℛ₁))
    (hz : z ∈ Deformation.fontaineHodge k p
      (Algebra.TensorProduct.includeRight : ℛ₁ →ₐ[𝓞] TensorProduct 𝓞 k ℛ₁).toRingHom) :
    ∃ y ∈ Deformation.fontaineHodge k p
        (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom,
      Deformation.DieudonneModule.map k p (Bialgebra.TensorProduct.map (BialgHom.id k k) π) y = z :=
  Deformation.FontaineLSurj.forall_exists_mem_fontaineHodge_map_eq p hp hk hker ℛ hrank hunip ℛ₁ hrank₁
    π hπ z hz

end S_Deformation_DieudonneModule_exists_mem_fontaineHodge_map_eq_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_mem_fontaineHodge_map_eq_of_isLocalRing_cartierDual (solution)
