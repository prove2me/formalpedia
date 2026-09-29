-- Prove2me | solution 1 for CohCarrier.heckeDiamondRing.exists_ringHom_ker_eq_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4c26e479-fa07-5b98-bf29-2ed87386046b

import Definitions.Def_CohCarrier_HeckeDiamondRing
import Definitions.Def_CuspForm_TWLevelHeckeRing
import Theorems.Thm_CohCarrier_H1_moduleFinite
import Theorems.Thm_CohCarrier_heckeT_comp_coeff
import Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
import Theorems.Thm_DeligneSerre_OperatorAlgebra_exists_eigenvector_baseChange_of_algHom
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector
p2m_attr_erase "instance" "CohCarrier.GammaHLower_finiteIndex"
p2m_attr_erase "simp" "CohCarrier.uMat_apply_10 CohCarrier.rightQuotEquivOfDvd_apply CohCarrier.uMat_apply_11 CohCarrier.uMat_apply_01 CohCarrier.uMat_apply_00 CohCarrier.coe_uElt"

set_option autoImplicit false

open scoped MatrixGroups TensorProduct

namespace CohCarrier
p2m_export "CohCarrier" "heckeTFamily_apply heckeDiamondGens heckeDiamondRing heckeDiamondRing.T heckeDiamondRing.coe_T heckeDiamondRing.diamond heckeDiamondRing.coe_diamond heckeTL heckeTL_apply gamma0Units_surjective diamondL diamondL_eq_diamondRaw gamma0Units val_gamma0Units GammaH mem_GammaH_iff H1 heckeT diamondL_mul diamondL_one diamondL_comm H1_moduleFinite heckeT_comp_coeff heckeT_diamondRaw_comm"
namespace heckeDiamondRing
p2m_export "CohCarrier.heckeDiamondRing" "T coe_T diamond coe_diamond"
namespace PointEigenvector
p2m_open "CohCarrier.heckeDiamondRing CohCarrier"

section Group

open CongruenceSubgroup

theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have hA0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨hA0, ?_⟩
  have h1 : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    exact hA'.2.2.2
  rw [h1]
  exact one_mem H

theorem isCongruenceSubgroup_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    IsCongruenceSubgroup (CohCarrier.GammaH M H) :=
  ⟨M, NeZero.ne M, Gamma_le_GammaH M H⟩

scoped instance finiteIndex_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  (isCongruenceSubgroup_GammaH M H).finiteIndex

scoped instance fg_SL2Z : Group.FG SL(2, ℤ) := by
  rw [Group.fg_iff]
  exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
    Set.toFinite _⟩

scoped instance fg_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : Group.FG ↥(CohCarrier.GammaH M H) :=
  inferInstance

theorem exists_finset_closure_eq_top (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ s : Finset ↥(CohCarrier.GammaH M H), Subgroup.closure (s : Set ↥(CohCarrier.GammaH M H)) = ⊤ := by
  obtain ⟨s, hs⟩ := (Group.fg_def.mp (fg_GammaH M H))
  exact ⟨s, hs⟩

theorem H1_eq_of_eqOn {M : ℕ} {H : Subgroup (ZMod M)ˣ} {A : Type*} [AddCommGroup A]
    (s : Set ↥(CohCarrier.GammaH M H)) (hs : Subgroup.closure s = ⊤)
    (φ ψ : CohCarrier.H1 M H A) (h : ∀ g ∈ s, φ (Additive.ofMul g) = ψ (Additive.ofMul g)) :
    φ = ψ := by
  let K : Subgroup ↥(CohCarrier.GammaH M H) :=
    { carrier := {g | φ (Additive.ofMul g) = ψ (Additive.ofMul g)}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, ofMul_mul, map_add] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq, ofMul_inv, map_neg] at ha ⊢
        rw [ha] }
  have hK : (⊤ : Subgroup ↥(CohCarrier.GammaH M H)) ≤ K := by
    rw [← hs, Subgroup.closure_le]
    exact h
  ext g
  exact hK (Subgroup.mem_top (Additive.toMul g))

end Group

section Coeff

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

scoped instance isTorsionFree_H1 (𝒪 : Type) [CommRing 𝒪] : Module.IsTorsionFree 𝒪 (CohCarrier.H1 M H 𝒪) :=
  Function.Injective.moduleIsTorsionFree
    (fun φ : CohCarrier.H1 M H 𝒪 => (φ : Additive ↥(CohCarrier.GammaH M H) → 𝒪))
    DFunLike.coe_injective (fun _ _ => rfl)

variable {𝒪 : Type} [CommRing 𝒪] {F : Type} [Field F] [Algebra 𝒪 F]

noncomputable def coeffBil : F →ₗ[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[𝒪] CohCarrier.H1 M H F :=
  LinearMap.mk₂ 𝒪
    (fun (c : F) (φ : CohCarrier.H1 M H 𝒪) =>
      (AddMonoidHom.mulLeft c).comp ((algebraMap 𝒪 F).toAddMonoidHom.comp φ))
    (fun c c' φ => AddMonoidHom.ext fun γ => by simp [add_mul])
    (fun a c φ => AddMonoidHom.ext fun γ => by simp [Algebra.smul_def, mul_assoc])
    (fun c φ ψ => AddMonoidHom.ext fun γ => by simp [mul_add])
    (fun a c φ => AddMonoidHom.ext fun γ => by
      show c * algebraMap 𝒪 F ((a • φ) γ) = a • (c * algebraMap 𝒪 F (φ γ))
      rw [AddMonoidHom.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
      ring)

@[scoped simp] theorem coeffBil_apply (c : F) (φ : CohCarrier.H1 M H 𝒪) (γ : Additive ↥(CohCarrier.GammaH M H)) :
    coeffBil M H c φ γ = c * algebraMap 𝒪 F (φ γ) := rfl

noncomputable def coeffMapₒ : F ⊗[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[𝒪] CohCarrier.H1 M H F :=
  TensorProduct.lift (coeffBil M H)

theorem coeffMapₒ_tmul (c : F) (φ : CohCarrier.H1 M H 𝒪) :
    coeffMapₒ M H (c ⊗ₜ φ) = coeffBil M H c φ :=
  TensorProduct.lift.tmul c φ

noncomputable def coeffMap : F ⊗[𝒪] CohCarrier.H1 M H 𝒪 →ₗ[F] CohCarrier.H1 M H F where
  toFun := coeffMapₒ M H
  map_add' x y := map_add _ x y
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c φ =>
      rw [TensorProduct.smul_tmul', coeffMapₒ_tmul, coeffMapₒ_tmul, RingHom.id_apply]
      refine AddMonoidHom.ext fun γ => ?_
      show (a • c) * algebraMap 𝒪 F (φ γ) = a • (c * algebraMap 𝒪 F (φ γ))
      rw [smul_eq_mul, smul_eq_mul, mul_assoc]
    | add x y hx hy =>
      simp only [smul_add, map_add, RingHom.id_apply] at hx hy ⊢
      rw [hx, hy]

theorem coeffMap_tmul (c : F) (φ : CohCarrier.H1 M H 𝒪) :
    coeffMap M H (c ⊗ₜ φ) = coeffBil M H c φ :=
  coeffMapₒ_tmul M H c φ

theorem coeffMap_heckeT (ℓ : ℕ) [NeZero ℓ] (x : F ⊗[𝒪] CohCarrier.H1 M H 𝒪) :
    coeffMap M H ((CohCarrier.heckeTL M H 𝒪 ℓ).baseChange F x) =
      CohCarrier.heckeT M H ℓ F (coeffMap M H x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c φ =>
    rw [LinearMap.baseChange_tmul, coeffMap_tmul, coeffMap_tmul, CohCarrier.heckeTL_apply]
    show (AddMonoidHom.mulLeft c).comp ((algebraMap 𝒪 F).toAddMonoidHom.comp
        (CohCarrier.heckeT M H ℓ 𝒪 φ)) = CohCarrier.heckeT M H ℓ F
        ((AddMonoidHom.mulLeft c).comp ((algebraMap 𝒪 F).toAddMonoidHom.comp φ))
    rw [← CohCarrier.heckeT_comp_coeff, ← CohCarrier.heckeT_comp_coeff]
  | add x y hx hy => rw [map_add, map_add, hx, hy, (coeffMap M H).map_add, map_add]

theorem coeffMap_diamondL [NeZero M] (u : (ZMod M)ˣ) (x : F ⊗[𝒪] CohCarrier.H1 M H 𝒪) :
    coeffMap M H ((CohCarrier.diamondL M H 𝒪 u).baseChange F x) =
      CohCarrier.diamondL M H F u (coeffMap M H x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c φ =>
    rw [LinearMap.baseChange_tmul, coeffMap_tmul, coeffMap_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, (coeffMap M H).map_add, map_add]

theorem coeffMap_injective [NeZero M] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    (hF : Function.Injective (algebraMap 𝒪 F)) : Function.Injective (coeffMap M H (𝒪 := 𝒪) (F := F)) := by
  classical
  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI : Module.Finite 𝒪 (CohCarrier.H1 M H 𝒪) := CohCarrier.H1_moduleFinite M H 𝒪 𝒪
  haveI : Module.Free 𝒪 (CohCarrier.H1 M H 𝒪) := inferInstance
  haveI : FaithfulSMul 𝒪 F := (faithfulSMul_iff_algebraMap_injective 𝒪 F).mpr hF
  obtain ⟨s, hs⟩ := exists_finset_closure_eq_top M H
  let b := Module.Free.chooseBasis 𝒪 (CohCarrier.H1 M H 𝒪)
  let bF := Algebra.TensorProduct.basis F b

  let v : Module.Free.ChooseBasisIndex 𝒪 (CohCarrier.H1 M H 𝒪) → (↥(s : Set ↥(CohCarrier.GammaH M H)) → 𝒪) :=
    fun i g => b i (Additive.ofMul (g : ↥(CohCarrier.GammaH M H)))
  have hv : LinearIndependent 𝒪 v := by
    rw [Fintype.linearIndependent_iff]
    intro y hy
    have hzero : ∑ i, y i • b i = 0 := by
      apply H1_eq_of_eqOn (s : Set ↥(CohCarrier.GammaH M H)) hs
      intro g hg
      have := congr_fun hy ⟨g, hg⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
      rw [AddMonoidHom.finsetSum_apply, AddMonoidHom.zero_apply]
      simpa [AddMonoidHom.smul_apply] using this
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) y hzero
  have hli := (linearIndependent_algebraMap_comp_iff (S := F)).mpr hv
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hxrepr : x = ∑ i, bF.repr x i • ((1 : F) ⊗ₜ b i) := by
    conv_lhs => rw [← bF.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
  have hcoef : ∑ i, bF.repr x i • (algebraMap 𝒪 F ∘ v i) = 0 := by
    ext ⟨g, hg⟩
    have h1 := congrArg (fun ψ : CohCarrier.H1 M H F => ψ (Additive.ofMul g)) hx
    simp only [AddMonoidHom.zero_apply] at h1
    rw [hxrepr, map_sum, AddMonoidHom.finsetSum_apply] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, AddMonoidHom.smul_apply, coeffMap_tmul, coeffBil_apply, one_mul, smul_eq_mul]
  have hd : ∀ i, bF.repr x i = 0 := fun i =>
    (Fintype.linearIndependent_iff.mp hli) (fun i => bF.repr x i) hcoef i
  rw [hxrepr]
  simp [hd]

end Coeff

section Iota

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (𝒪 : Type) [CommRing 𝒪]

def iotaM : CohCarrier.H1 M H ℤ →ₗ[ℤ] CohCarrier.H1 M H 𝒪 where
  toFun ψ := (Int.castAddHom 𝒪).comp ψ
  map_add' ψ ψ' := by ext; simp
  map_smul' n ψ := by
    refine AddMonoidHom.ext fun γ => ?_
    rw [RingHom.id_apply]
    simp only [AddMonoidHom.coe_comp, Int.coe_castAddHom, Function.comp_apply, AddMonoidHom.smul_apply,
      Int.cast_mul, zsmul_eq_mul]
    simp

@[scoped simp] theorem iotaM_apply (ψ : CohCarrier.H1 M H ℤ) (γ : Additive ↥(CohCarrier.GammaH M H)) :
    iotaM M H 𝒪 ψ γ = ((ψ γ : ℤ) : 𝒪) := rfl

theorem iotaM_injective [CharZero 𝒪] : Function.Injective (iotaM M H 𝒪) := by
  intro ψ ψ' h
  ext γ
  have := congrArg (fun φ : CohCarrier.H1 M H 𝒪 => φ γ) h
  simp at this
  exact this

theorem heckeT_iotaM (ℓ : ℕ) [NeZero ℓ] (ψ : CohCarrier.H1 M H ℤ) :
    CohCarrier.heckeT M H ℓ 𝒪 (iotaM M H 𝒪 ψ) = iotaM M H 𝒪 (CohCarrier.heckeT M H ℓ ℤ ψ) :=
  CohCarrier.heckeT_comp_coeff M H ℓ (Int.castAddHom 𝒪) ψ

theorem diamondL_iotaM [NeZero M] (u : (ZMod M)ˣ) (ψ : CohCarrier.H1 M H ℤ) :
    CohCarrier.diamondL M H 𝒪 u (iotaM M H 𝒪 ψ) = iotaM M H 𝒪 (CohCarrier.diamondL M H ℤ u ψ) :=
  rfl

theorem exists_sum_smul_iotaM [NeZero M] [IsDomain 𝒪] [CharZero 𝒪] (φ : CohCarrier.H1 M H 𝒪) :
    ∃ (n : ℕ) (c : Fin n → 𝒪) (ψ : Fin n → CohCarrier.H1 M H ℤ),
      φ = ∑ i, c i • iotaM M H 𝒪 (ψ i) := by
  classical
  let L : AddSubgroup 𝒪 := AddMonoidHom.range φ
  haveI : AddGroup.FG ↥L := AddGroup.fg_range φ
  haveI : Module.Finite ℤ ↥L := Module.Finite.iff_addGroup_fg.mpr inferInstance
  haveI : Module.IsTorsionFree ℤ ↥L :=
    Function.Injective.moduleIsTorsionFree (fun x : ↥L => (x : 𝒪)) Subtype.val_injective
      (fun c x => by simp)
  haveI : Module.Free ℤ ↥L := inferInstance
  let b := Module.Free.chooseBasis ℤ ↥L
  let e := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ ↥L)
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥L),
    fun j => ((b (e.symm j) : ↥L) : 𝒪),
    fun j => (b.coord (e.symm j)).toAddMonoidHom.comp φ.rangeRestrict, ?_⟩
  refine AddMonoidHom.ext fun γ => ?_
  rw [AddMonoidHom.finsetSum_apply]
  simp only [AddMonoidHom.smul_apply, iotaM_apply, AddMonoidHom.coe_comp, Function.comp_apply,
    LinearMap.toAddMonoidHom_coe, Module.Basis.coord_apply, smul_eq_mul]
  have h := b.sum_repr (φ.rangeRestrict γ)
  have h' := congrArg (fun x : ↥L => (x : 𝒪)) h
  simp only [AddSubmonoidClass.coe_finsetSum, AddSubgroupClass.coe_zsmul,
    AddMonoidHom.coe_rangeRestrict, zsmul_eq_mul] at h'
  rw [← h']
  rw [← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

end Iota

section Commute

open CongruenceSubgroup

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem exists_gamma0_lift (ℓ : ℕ) [NeZero ℓ] (u : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 ∧ CohCarrier.gamma0Units M σ = u := by
  haveI : NeZero (ℓ * M) := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne M)⟩
  have hdvd : M ∣ ℓ * M := dvd_mul_left M ℓ
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hdvd u
  obtain ⟨τ, hτ⟩ := CohCarrier.gamma0Units_surjective (ℓ * M) v
  have hτ10 : ((ℓ * M : ℕ) : ℤ) ∣ (τ : SL(2, ℤ)) 1 0 := by
    have h := τ.2
    rw [Gamma0_mem] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hτM : (τ : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((Int.natCast_dvd_natCast.mpr hdvd).trans hτ10)
  refine ⟨⟨(τ : SL(2, ℤ)), hτM⟩, hτ10, ?_⟩
  apply Units.ext
  rw [CohCarrier.val_gamma0Units, ← hv, ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ← hτ,
    CohCarrier.val_gamma0Units]
  show (((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ZMod.castHom hdvd (ZMod M) (((τ : SL(2, ℤ)) 1 1 : ℤ) : ZMod (ℓ * M))
  rw [map_intCast]

theorem heckeTL_comm_diamondL (A : Type) [CommRing A] (ℓ : ℕ) [NeZero ℓ] (u : (ZMod M)ˣ) :
    CohCarrier.heckeTL M H A ℓ * CohCarrier.diamondL M H A u =
      CohCarrier.diamondL M H A u * CohCarrier.heckeTL M H A ℓ := by
  obtain ⟨σ, hσ, hσu⟩ := exists_gamma0_lift M ℓ u
  apply LinearMap.ext
  intro φ
  rw [Module.End.mul_apply, Module.End.mul_apply, CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply,
    CohCarrier.diamondL_eq_diamondRaw M H A u σ hσu, CohCarrier.diamondL_eq_diamondRaw M H A u σ hσu]
  exact CohCarrier.heckeT_diamondRaw_comm M H ℓ σ hσ φ

end Commute

section Restrict

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (H' : Subgroup (ZMod M)ˣ)
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]

omit [IsDomain 𝒪] [CharZero 𝒪] in

theorem exists_restrict (t : Module.End 𝒪 (CohCarrier.H1 M H 𝒪))
    (ht : t ∈ CohCarrier.heckeDiamondRing M H S H' 𝒪) :
    ∃ t' : Module.End ℤ (CohCarrier.H1 M H ℤ), ∀ ψ, t (iotaM M H 𝒪 ψ) = iotaM M H 𝒪 (t' ψ) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, rfl⟩ | ⟨u, rfl⟩)
    · haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
      refine ⟨CohCarrier.heckeTL M H ℤ ℓ.1, fun ψ => ?_⟩
      rw [CohCarrier.heckeTFamily_apply, CohCarrier.heckeTL_apply]
      exact heckeT_iotaM M H 𝒪 ℓ.1 ψ
    · exact ⟨CohCarrier.diamondL M H ℤ (u : (ZMod M)ˣ), fun ψ => rfl⟩
  · intro n
    refine ⟨algebraMap ℤ _ n, fun ψ => ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, LinearMap.map_smul_of_tower]
  · rintro x y - - ⟨x', hx'⟩ ⟨y', hy'⟩
    exact ⟨x' + y', fun ψ => by rw [LinearMap.add_apply, hx', hy', LinearMap.add_apply, map_add]⟩
  · rintro x y - - ⟨x', hx'⟩ ⟨y', hy'⟩
    exact ⟨x' * y', fun ψ => by rw [Module.End.mul_apply, hy', hx', Module.End.mul_apply]⟩

theorem restrict_unique {M : ℕ} {H : Subgroup (ZMod M)ˣ} {𝒪 : Type} [CommRing 𝒪] [CharZero 𝒪]
    {t₁ t₂ : Module.End ℤ (CohCarrier.H1 M H ℤ)}
    (h : ∀ ψ, iotaM M H 𝒪 (t₁ ψ) = iotaM M H 𝒪 (t₂ ψ)) : t₁ = t₂ :=
  LinearMap.ext fun ψ => iotaM_injective M H 𝒪 (h ψ)

noncomputable def resRingHom :
    ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪) →+* Module.End ℤ (CohCarrier.H1 M H ℤ) where
  toFun t := Classical.choose (exists_restrict M H S H' 𝒪 t.1 t.2)
  map_one' := by
    refine restrict_unique (𝒪 := 𝒪) fun ψ => ?_
    rw [← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ (1 : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)).2)]
    rfl
  map_mul' t s := by
    refine restrict_unique (𝒪 := 𝒪) fun ψ => ?_
    rw [← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ (t * s).2), Module.End.mul_apply,
      ← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ t.2),
      ← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ s.2)]
    rfl
  map_zero' := by
    refine restrict_unique (𝒪 := 𝒪) fun ψ => ?_
    rw [← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ (0 : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)).2),
      LinearMap.zero_apply, map_zero]
    rfl
  map_add' t s := by
    refine restrict_unique (𝒪 := 𝒪) fun ψ => ?_
    rw [← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ (t + s).2), LinearMap.add_apply, map_add,
      ← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ t.2),
      ← Classical.choose_spec (exists_restrict M H S H' 𝒪 _ s.2)]
    rfl

omit [IsDomain 𝒪] in
theorem iotaM_resRingHom (t : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) (ψ : CohCarrier.H1 M H ℤ) :
    iotaM M H 𝒪 (resRingHom M H S H' 𝒪 t ψ) = (t : Module.End 𝒪 (CohCarrier.H1 M H 𝒪)) (iotaM M H 𝒪 ψ) :=
  (Classical.choose_spec (exists_restrict M H S H' 𝒪 t.1 t.2) ψ).symm

noncomputable def res :
    ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪) →ₐ[ℤ] Module.End ℤ (CohCarrier.H1 M H ℤ) :=
  { resRingHom M H S H' 𝒪 with
    commutes' := fun n => by
      show resRingHom M H S H' 𝒪 (algebraMap ℤ _ n) = algebraMap ℤ _ n
      rw [eq_intCast, eq_intCast, map_intCast] }

omit [IsDomain 𝒪] in
theorem res_apply (t : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) :
    res M H S H' 𝒪 t = resRingHom M H S H' 𝒪 t := rfl

omit [IsDomain 𝒪] in

theorem iotaM_res (t : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) (ψ : CohCarrier.H1 M H ℤ) :
    iotaM M H 𝒪 (res M H S H' 𝒪 t ψ) = (t : Module.End 𝒪 (CohCarrier.H1 M H 𝒪)) (iotaM M H 𝒪 ψ) :=
  (Classical.choose_spec (exists_restrict M H S H' 𝒪 t.1 t.2) ψ).symm

theorem res_injective : Function.Injective (res M H S H' 𝒪) := by
  intro t s h
  apply Subtype.ext
  apply LinearMap.ext
  intro φ
  obtain ⟨n, c, ψ, rfl⟩ := exists_sum_smul_iotaM M H 𝒪 φ
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, ← iotaM_res, ← iotaM_res, h]

omit [IsDomain 𝒪] in
theorem res_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    res M H S H' 𝒪 (CohCarrier.heckeDiamondRing.T M H S H' 𝒪 ℓ hℓ hℓS hℓM) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeTL M H ℤ ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine restrict_unique (𝒪 := 𝒪) fun ψ => ?_
  rw [iotaM_res, CohCarrier.heckeDiamondRing.coe_T, CohCarrier.heckeTL_apply, CohCarrier.heckeTL_apply,
    heckeT_iotaM]

omit [IsDomain 𝒪] in
theorem res_diamond (u : (ZMod M)ˣ) (hu : u ∈ H') :
    res M H S H' 𝒪 (CohCarrier.heckeDiamondRing.diamond M H S H' 𝒪 u hu) = CohCarrier.diamondL M H ℤ u := by
  refine restrict_unique (𝒪 := 𝒪) fun ψ => ?_
  rw [iotaM_res, CohCarrier.heckeDiamondRing.coe_diamond]
  rfl

omit [IsDomain 𝒪] [CharZero 𝒪] in

theorem coe_comm_diamondL (t : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) (u : (ZMod M)ˣ) :
    (t : Module.End 𝒪 (CohCarrier.H1 M H 𝒪)) * CohCarrier.diamondL M H 𝒪 u =
      CohCarrier.diamondL M H 𝒪 u * (t : Module.End 𝒪 (CohCarrier.H1 M H 𝒪)) := by
  have hle : CohCarrier.heckeDiamondRing M H S H' 𝒪 ≤
      Subalgebra.centralizer ℤ (Set.range fun v : (ZMod M)ˣ => CohCarrier.diamondL M H 𝒪 v) := by
    refine Algebra.adjoin_le ?_
    rintro a (⟨ℓ, rfl⟩ | ⟨w, rfl⟩)
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨v, rfl⟩
      haveI : NeZero ℓ.1 := ⟨ℓ.2.1.ne_zero⟩
      exact (heckeTL_comm_diamondL M H 𝒪 ℓ.1 v).symm
    · rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro _ ⟨v, rfl⟩
      exact CohCarrier.diamondL_comm M H 𝒪 v w
  exact ((Subalgebra.mem_centralizer_iff ℤ).mp (hle t.2) _ ⟨u, rfl⟩).symm

omit [IsDomain 𝒪] in

theorem res_comm_diamondL (t : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) (u : (ZMod M)ˣ) :
    CohCarrier.diamondL M H ℤ u * res M H S H' 𝒪 t = res M H S H' 𝒪 t * CohCarrier.diamondL M H ℤ u := by
  apply LinearMap.ext
  intro ψ
  apply iotaM_injective M H 𝒪
  rw [Module.End.mul_apply, Module.End.mul_apply, ← diamondL_iotaM, iotaM_res, iotaM_res,
    ← diamondL_iotaM, ← Module.End.mul_apply, ← coe_comm_diamondL, Module.End.mul_apply]

theorem addGroup_fg : AddGroup.FG ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪) := by
  haveI : Module.Finite ℤ (CohCarrier.H1 M H ℤ) := CohCarrier.H1_moduleFinite M H ℤ ℤ
  haveI : Module.Free ℤ (CohCarrier.H1 M H ℤ) := inferInstance
  haveI : Module.Finite ℤ (Module.End ℤ (CohCarrier.H1 M H ℤ)) := inferInstance
  have h := Module.Finite.of_injective (res M H S H' 𝒪).toLinearMap
    (fun _ _ hab => res_injective M H S H' 𝒪 hab)
  have h' : Module.Finite ℤ ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪) := by convert h
  exact (Module.Finite.iff_addGroup_fg (G := ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪))).mp h'

end Restrict

section Ring

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (H' : Subgroup (ZMod M)ˣ)
  (𝒪 : Type) [CommRing 𝒪]

noncomputable def dia (A : Type) [CommRing A] : (ZMod M)ˣ →* Module.End A (CohCarrier.H1 M H A) where
  toFun u := CohCarrier.diamondL M H A u
  map_one' := CohCarrier.diamondL_one M H A
  map_mul' u v := CohCarrier.diamondL_mul M H A u v

theorem dia_apply (A : Type) [CommRing A] (u : (ZMod M)ˣ) : dia M H A u = CohCarrier.diamondL M H A u := rfl

abbrev commRingOfComm
    (hcomm : ∀ a ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪, ∀ b ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪,
      a * b = b * a) :
    CommRing ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪) :=
  { (CohCarrier.heckeDiamondRing M H S H' 𝒪).toRing with
    mul_comm := (Algebra.isMulCommutative_adjoin ℤ hcomm).is_comm.comm }

theorem exists_ringHom_ker_eq {T : Type} [CommRing T] [AddGroup.FG T] (𝔭 : Ideal T) [𝔭.IsPrime]
    (h𝔭 : ∀ n : ℤ, (n : T) ∈ 𝔭 → n = 0) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] :
    ∃ χ : T →+* Ω, RingHom.ker χ = 𝔭 := by
  haveI : IsDomain (T ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  haveI : CharZero (T ⧸ 𝔭) := ⟨fun a b hab => by
    have h1 : Ideal.Quotient.mk 𝔭 ((a : ℤ) : T) = Ideal.Quotient.mk 𝔭 ((b : ℤ) : T) := by
      rw [map_intCast, map_intCast, Int.cast_natCast, Int.cast_natCast]
      exact hab
    rw [Ideal.Quotient.eq, ← Int.cast_sub] at h1
    have h2 := h𝔭 _ h1
    omega⟩
  have hfgQ : AddGroup.FG (T ⧸ 𝔭) :=
    AddGroup.fg_of_surjective (f := (Ideal.Quotient.mk 𝔭).toAddMonoidHom) Ideal.Quotient.mk_surjective
  have hfin : Module.Finite ℤ (T ⧸ 𝔭) := Module.Finite.iff_addGroup_fg.mpr hfgQ
  haveI : Algebra.IsIntegral ℤ (T ⧸ 𝔭) := by
    have h : (Algebra.toModule : Module ℤ (T ⧸ 𝔭)) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
    have hfin' : @Module.Finite ℤ (T ⧸ 𝔭) _ _ Algebra.toModule := by rw [h]; exact hfin
    exact @Algebra.IsIntegral.of_finite ℤ (T ⧸ 𝔭) _ _ _ hfin'
  have instTF : @Module.IsTorsionFree ℤ (T ⧸ 𝔭) _ _ Algebra.toModule := by
    have h : (Algebra.toModule : Module ℤ (T ⧸ 𝔭)) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
    rw [h]
    infer_instance
  have instTFΩ : @Module.IsTorsionFree ℤ Ω _ _ Algebra.toModule := by
    have h : (Algebra.toModule : Module ℤ Ω) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
    rw [h]
    infer_instance
  let emb : (T ⧸ 𝔭) →ₐ[ℤ] Ω := @IsAlgClosed.lift Ω _ _ ℤ _ _ (T ⧸ 𝔭) _ _ _ _ instTF instTFΩ inferInstance
  have hker : RingHom.ker emb.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, eq_intCast, Int.cast_eq_zero] at hn
    rw [hn]
    exact Ideal.zero_mem _
  have hemb : Function.Injective emb.toRingHom := (RingHom.injective_iff_ker_eq_bot _).mpr hker
  refine ⟨emb.toRingHom.comp (Ideal.Quotient.mk 𝔭), ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply]
  constructor
  · intro hx
    have h0 : Ideal.Quotient.mk 𝔭 x = 0 := hemb (by rw [map_zero]; exact hx)
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  · intro hx
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

end Ring

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
  (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (H' : Subgroup (ZMod M)ˣ)

set_option quotPrecheck false in
local notation "𝕋" => ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)

theorem main
    (hcomm : ∀ a ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪, ∀ b ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪,
      a * b = b * a)
    (𝔭 : Ideal 𝕋) [𝔭.IsPrime]
    (h𝔭 : ∀ n : ℤ, (n : 𝕋) ∈ 𝔭 → n = 0)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] :
    ∃ (χ : 𝕋 →+* Ω) (e : (ZMod M)ˣ →* Ωˣ)
      (φ : CohCarrier.H1 M H Ω),
      RingHom.ker χ = 𝔭 ∧ φ ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ Ω φ) =
          χ (CohCarrier.heckeDiamondRing.T M H S H' 𝒪 ℓ hℓ hℓS hℓM) • φ) ∧
      (∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H Ω u φ = (e u : Ω) • φ) ∧
      (∀ (u : (ZMod M)ˣ) (hu : u ∈ H'),
        (e u : Ω) = χ (CohCarrier.heckeDiamondRing.diamond M H S H' 𝒪 u hu)) := by
  classical
  letI instCR : CommRing 𝕋 := commRingOfComm M H S H' 𝒪 hcomm

  haveI hfgT : AddGroup.FG 𝕋 := addGroup_fg M H S H' 𝒪
  obtain ⟨χ, hχ⟩ := exists_ringHom_ker_eq (T := 𝕋) 𝔭 h𝔭 Ω

  let lam : 𝕋 →ₐ[ℤ] Ω :=
    { χ with
      commutes' := fun n => by
        show χ (algebraMap ℤ _ n) = algebraMap ℤ Ω n
        rw [eq_intCast, eq_intCast, map_intCast] }
  have hlam : ∀ x : 𝕋, lam x = χ x := fun x => rfl

  haveI : Module.Finite ℤ (CohCarrier.H1 M H ℤ) := CohCarrier.H1_moduleFinite M H ℤ ℤ
  have hZ : Function.Injective (algebraMap ℤ Ω) := (algebraMap ℤ Ω).injective_int
  obtain ⟨e, w, hw0, hT, hD⟩ :=
    DeligneSerre.OperatorAlgebra.exists_eigenvector_baseChange_of_algHom
      (res M H S H' 𝒪) (res_injective M H S H' 𝒪)
      (dia M H ℤ) (fun u t => res_comm_diamondL M H S H' 𝒪 t u) hZ lam
  have hT' : ∀ t : 𝕋, (res M H S H' 𝒪 t).baseChange Ω w = χ t • w := hT

  let U := coeffMap M H (𝒪 := ℤ) (F := Ω)
  have hUinj : Function.Injective U := coeffMap_injective M H hZ
  refine ⟨χ, e, U w, hχ, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hw0 (hUinj (by rw [h, map_zero]))
  · intro ℓ hℓ hℓS hℓM
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have h1 := hT' (CohCarrier.heckeDiamondRing.T M H S H' 𝒪 ℓ hℓ hℓS hℓM)
    rw [res_T] at h1
    have h2 := congrArg U h1
    rw [map_smul, coeffMap_heckeT] at h2
    exact h2
  · intro u
    have h1 := congrArg U (hD u)
    rw [map_smul, dia_apply, coeffMap_diamondL] at h1
    exact h1
  · intro u hu
    have h1 := hT' (CohCarrier.heckeDiamondRing.diamond M H S H' 𝒪 u hu)
    rw [res_diamond] at h1
    have h2 := hD u
    rw [dia_apply, h1] at h2
    exact (smul_left_injective Ω hw0 h2).symm

end Main

end CohCarrier.heckeDiamondRing.PointEigenvector
p2m_reactivate "P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector.CohCarrier P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector.CohCarrier.heckeDiamondRing P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector.CohCarrier.heckeDiamondRing.PointEigenvector"
p2m_reactivate "P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector.CohCarrier P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector.CohCarrier.heckeDiamondRing"
p2m_reactivate "P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector.CohCarrier"

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (H' : Subgroup (ZMod M)ˣ)
    (hcomm : ∀ a ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪, ∀ b ∈ CohCarrier.heckeDiamondGens M H S H' 𝒪,
      a * b = b * a)
    (𝔭 : Ideal ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) [𝔭.IsPrime]
    (h𝔭 : ∀ n : ℤ, (n : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪)) ∈ 𝔭 → n = 0)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] :
    ∃ (χ : ↥(CohCarrier.heckeDiamondRing M H S H' 𝒪) →+* Ω) (e : (ZMod M)ˣ →* Ωˣ)
      (φ : CohCarrier.H1 M H Ω),
      RingHom.ker χ = 𝔭 ∧ φ ≠ 0 ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M),
        (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT M H ℓ Ω φ) =
          χ (CohCarrier.heckeDiamondRing.T M H S H' 𝒪 ℓ hℓ hℓS hℓM) • φ) ∧
      (∀ u : (ZMod M)ˣ, CohCarrier.diamondL M H Ω u φ = (e u : Ω) • φ) ∧
      (∀ (u : (ZMod M)ˣ) (hu : u ∈ H'),
        (e u : Ω) = χ (CohCarrier.heckeDiamondRing.diamond M H S H' 𝒪 u hu)) :=
  CohCarrier.heckeDiamondRing.PointEigenvector.main M H S H' hcomm 𝔭 h𝔭 Ω

end S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector
end P2MW
export P2MW.S_CohCarrier_heckeDiamondRing_exists_ringHom_ker_eq_eigenvector (solution)
