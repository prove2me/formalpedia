-- Prove2me | solution 1 for Deformation.DieudonneModule.eq_of_map_eq_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7f5d7552-3232-57d6-b8cd-0400de7f3c34

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_HopfAlgebra_map_antipode_comul_of_isCocomm
import Theorems.Thm_HopfAlgebra_exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual
import Theorems.Thm_HopfAlgebra_isLocalRing_cartierDual_of_surjective
import Theorems.Thm_HopfAlgebra_wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open WithConv TensorProduct Function Bialgebra

namespace DieudonneFaithful

section Antipode

variable (R : Type*) [CommRing R] (H : Type*) [CommRing H] [HopfAlgebra R H]

noncomputable def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode R) HopfAlgebra.antipode_one fun a b => by
    rw [HopfAlgebra.antipode_mul, mul_comm]

@[scoped simp] theorem antipodeAlgHom_apply (x : H) : antipodeAlgHom R H x = HopfAlgebra.antipode R x :=
  rfl

variable [Coalgebra.IsCocomm R H]

noncomputable def antipodeBialgHom : H →ₐc[R] H :=
  BialgHom.ofAlgHom (antipodeAlgHom R H)
    (by
      refine AlgHom.ext fun x => ?_
      simp [HopfAlgebra.counit_antipode])
    (by
      refine AlgHom.ext fun x => ?_
      change Algebra.TensorProduct.map (antipodeAlgHom R H) (antipodeAlgHom R H)
          (Coalgebra.comul (R := R) x) = Coalgebra.comul (R := R) (HopfAlgebra.antipode R x)
      rw [← HopfAlgebra.map_antipode_comul_of_isCocomm inferInstance x]
      rfl)

@[scoped simp] theorem antipodeBialgHom_apply (x : H) :
    antipodeBialgHom R H x = HopfAlgebra.antipode R x := rfl

theorem antipodeBialgHom_toAlgHom :
    (antipodeBialgHom R H : H →ₐ[R] H) = antipodeAlgHom R H := rfl

end Antipode

section postComp

variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {A A' : Type*} [Semiring A] [Algebra R A] [Semiring A'] [Algebra R A']

def postComp (g : A →ₐ[R] A') : WithConv (C →ₗ[R] A) →+* WithConv (C →ₗ[R] A') where
  toFun F := toConv (g.toLinearMap ∘ₗ F.ofConv)
  map_one' := by
    apply WithConv.ext
    ext c
    simp [LinearMap.convOne_def]
  map_mul' F G := by
    apply WithConv.ext
    simpa using LinearMap.algHom_comp_convMul_distrib g F G
  map_zero' := by
    apply WithConv.ext
    simp
  map_add' F G := by
    apply WithConv.ext
    simp [LinearMap.comp_add]

end postComp

section Points

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
  {A : Type*} [CommRing A] [Algebra R A]

lemma id_convMul_antipode :
    toConv (LinearMap.id : H →ₗ[R] H) * toConv (HopfAlgebra.antipode R) = 1 := by
  apply WithConv.ext
  change LinearMap.mul' R H ∘ₗ TensorProduct.map LinearMap.id (HopfAlgebra.antipode R) ∘ₗ
    Coalgebra.comul = _
  exact HopfAlgebra.mul_antipode_lTensor_comul

lemma antipode_convMul_id :
    toConv (HopfAlgebra.antipode R) * toConv (LinearMap.id : H →ₗ[R] H) = 1 := by
  apply WithConv.ext
  change LinearMap.mul' R H ∘ₗ TensorProduct.map (HopfAlgebra.antipode R) LinearMap.id ∘ₗ
    Coalgebra.comul = _
  exact HopfAlgebra.mul_antipode_rTensor_comul

lemma toLinearMap_convMul_comp_antipode (g : H →ₐ[R] A) :
    toConv g.toLinearMap * toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) = 1 := by
  have h1 : postComp g (toConv (LinearMap.id : H →ₗ[R] H)) = toConv g.toLinearMap := rfl
  have h2 : postComp g (toConv (HopfAlgebra.antipode R)) =
      toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) := rfl
  rw [← h1, ← h2, ← map_mul, id_convMul_antipode, map_one]

lemma comp_antipode_convMul_toLinearMap (g : H →ₐ[R] A) :
    toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) * toConv g.toLinearMap = 1 := by
  have h1 : postComp g (toConv (LinearMap.id : H →ₗ[R] H)) = toConv g.toLinearMap := rfl
  have h2 : postComp g (toConv (HopfAlgebra.antipode R)) =
      toConv (g.toLinearMap ∘ₗ HopfAlgebra.antipode R) := rfl
  rw [← h1, ← h2, ← map_mul, antipode_convMul_id, map_one]

lemma point_mul_comp_antipode (g : WithConv (H →ₐ[R] A)) :
    g * toConv (g.ofConv.comp (antipodeAlgHom R H)) = 1 := by
  apply toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)
  change toConv (g * toConv (g.ofConv.comp (antipodeAlgHom R H))).ofConv.toLinearMap =
    toConv (1 : WithConv (H →ₐ[R] A)).ofConv.toLinearMap
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  exact toLinearMap_convMul_comp_antipode g.ofConv

lemma comp_antipode_mul_point (g : WithConv (H →ₐ[R] A)) :
    toConv (g.ofConv.comp (antipodeAlgHom R H)) * g = 1 := by
  apply toConv_injective.comp (AlgHom.toLinearMap_injective.comp ofConv_injective)
  change toConv (toConv (g.ofConv.comp (antipodeAlgHom R H)) * g).ofConv.toLinearMap =
    toConv (1 : WithConv (H →ₐ[R] A)).ofConv.toLinearMap
  rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne]
  exact comp_antipode_convMul_toLinearMap g.ofConv

end Points

section Witt

variable {k : Type*} [CommRing k] {p : ℕ} [Fact p.Prime] {n : ℕ}
  {B : Type*} [CommRing B] [HopfAlgebra k B]
  {A : Type*} [CommRing A] [Algebra k A]

open Deformation Deformation.TruncWitt

lemma map_convOne_of_mem_wittHom {x : TruncatedWittVector p n B} (hx : x ∈ wittHom k p n B) :
    TruncWitt.map (1 : WithConv (B →ₐ[k] A)).ofConv.toRingHom x = 0 := by
  have hfac : (1 : WithConv (B →ₐ[k] A)).ofConv.toRingHom =
      (algebraMap k A).comp (Bialgebra.counitAlgHom k B).toRingHom := by
    refine RingHom.ext fun c => ?_
    simp [AlgHom.convOne_apply]
  rw [hfac, ← TruncWitt.map_map, map_counit_of_mem_wittHom hx, map_zero]

lemma map_antipode_of_mem_wittHom {x : TruncatedWittVector p n B} (hx : x ∈ wittHom k p n B) :
    TruncWitt.map (antipodeAlgHom k B).toRingHom x = -x := by
  have h := map_convMul_of_mem_wittHom (T := B) hx (toConv (AlgHom.id k B))
    (toConv ((toConv (AlgHom.id k B)).ofConv.comp (antipodeAlgHom k B)))
  rw [point_mul_comp_antipode, map_convOne_of_mem_wittHom hx] at h

  have hid : TruncWitt.map (toConv (AlgHom.id k B)).ofConv.toRingHom x = x := by
    change TruncWitt.map (AlgHom.id k B).toRingHom x = x
    exact TruncWitt.map_id x
  rw [hid] at h
  have : TruncWitt.map ((toConv (AlgHom.id k B)).ofConv.comp (antipodeAlgHom k B)).toRingHom x =
      TruncWitt.map (antipodeAlgHom k B).toRingHom x := rfl
  rw [← this]
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma map_convMul_comp_antipode_of_mem_wittHom {x : TruncatedWittVector p n B}
    (hx : x ∈ wittHom k p n B) (g g' : B →ₐ[k] A) :
    TruncWitt.map (toConv g * toConv (g'.comp (antipodeAlgHom k B))).ofConv.toRingHom x =
      TruncWitt.map g.toRingHom x - TruncWitt.map g'.toRingHom x := by
  rw [map_convMul_of_mem_wittHom hx, ofConv_toConv, ofConv_toConv, sub_eq_add_neg]
  congr 1
  change TruncWitt.map (g'.toRingHom.comp (antipodeAlgHom k B).toRingHom) x = _
  rw [← TruncWitt.map_map, map_antipode_of_mem_wittHom hx, map_neg]

end Witt

namespace KerQuot

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Bialgebra k B]
  {A : Type*} [CommRing A] [Bialgebra k A] (d : B →ₐc[k] A)

abbrev kerIdeal : Ideal B := RingHom.ker (d : B →ₐ[k] A)

noncomputable def iota : B ⧸ kerIdeal d →ₐ[k] A := Ideal.kerLiftAlg (d : B →ₐ[k] A)

theorem iota_mk (x : B) : iota d (Ideal.Quotient.mk (kerIdeal d) x) = d x :=
  Ideal.kerLiftAlg_mk _ _

theorem iota_injective : Injective (iota d) := Ideal.kerLiftAlg_injective _

theorem iota_comp_mkₐ : (iota d).comp (Ideal.Quotient.mkₐ k (kerIdeal d)) = (d : B →ₐ[k] A) :=
  AlgHom.ext fun x => iota_mk d x

private theorem map_apply_eq_linearMap {A' B' C D : Type*} [CommRing A'] [CommRing B']
    [CommRing C] [CommRing D] [Algebra k A'] [Algebra k B'] [Algebra k C] [Algebra k D]
    (f : A' →ₐ[k] C) (g : B' →ₐ[k] D) (z : A' ⊗[k] B') :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

theorem map_mkₐ_comul_eq_zero (x : B) (hx : x ∈ kerIdeal d) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal d)) (Ideal.Quotient.mkₐ k (kerIdeal d))
      (Coalgebra.comul (R := k) x) = 0 := by
  have hinj : Injective (Algebra.TensorProduct.map (iota d) (iota d)) := by
    intro z w hzw
    rw [map_apply_eq_linearMap, map_apply_eq_linearMap] at hzw
    exact TensorProduct.map_injective_of_flat_flat _ _ (iota_injective d) (iota_injective d) hzw
  apply hinj
  rw [map_zero, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, iota_comp_mkₐ]
  have h := AlgHom.congr_fun (BialgHom.map_comp_comulAlgHom d) x
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply] at h
  rw [h, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, RingHom.mem_ker.1 hx, map_zero]

theorem counit_eq_zero (x : B) (hx : x ∈ kerIdeal d) : Coalgebra.counit (R := k) x = 0 := by
  have hdx : d x = 0 := hx
  rw [← CoalgHomClass.counit_comp_apply d x, hdx, map_zero]

private noncomputable def _root_.DieudonneFaithful.KerQuot.comul : B ⧸ kerIdeal d →ₐ[k] (B ⧸ kerIdeal d) ⊗[k] (B ⧸ kerIdeal d) :=
  Ideal.Quotient.liftₐ (kerIdeal d)
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal d))
      (Ideal.Quotient.mkₐ k (kerIdeal d))).comp (comulAlgHom k B))
    (fun x hx => map_mkₐ_comul_eq_zero d x hx)

p2m_export "DieudonneFaithful.KerQuot" "comul"
theorem comul_comp_mkₐ :
    (comul d).comp (Ideal.Quotient.mkₐ k (kerIdeal d)) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal d))
        (Ideal.Quotient.mkₐ k (kerIdeal d))).comp (comulAlgHom k B) :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem comul_mk (x : B) :
    comul d (Ideal.Quotient.mk (kerIdeal d) x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal d)) (Ideal.Quotient.mkₐ k (kerIdeal d))
        (Coalgebra.comul (R := k) x) := rfl

private noncomputable def _root_.DieudonneFaithful.KerQuot.counit : B ⧸ kerIdeal d →ₐ[k] k :=
  Ideal.Quotient.liftₐ (kerIdeal d) (counitAlgHom k B) (fun x hx => counit_eq_zero d x hx)

p2m_export "DieudonneFaithful.KerQuot" "counit"
theorem counit_comp_mkₐ : (counit d).comp (Ideal.Quotient.mkₐ k (kerIdeal d)) = counitAlgHom k B :=
  Ideal.Quotient.liftₐ_comp _ _ _

@[scoped simp] theorem counit_mk (x : B) :
    counit d (Ideal.Quotient.mk (kerIdeal d) x) = Coalgebra.counit (R := k) x := rfl

private theorem _root_.DieudonneFaithful.KerQuot.rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit d) (.id k (B ⧸ kerIdeal d))).comp (comul d) =
      (Algebra.TensorProduct.lid k (B ⧸ kerIdeal d)).symm := by
  refine Ideal.Quotient.algHom_ext k ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (counitAlgHom k B).toLinearMap
      (Ideal.Quotient.mkₐ k (kerIdeal d)).toLinearMap
      = ((Ideal.Quotient.mkₐ k (kerIdeal d)).toLinearMap.lTensor k) ∘ₗ
          ((counitAlgHom k B).toLinearMap.rTensor B) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom k B).toLinearMap.rTensor B) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

p2m_export "DieudonneFaithful.KerQuot" "rTensor_counit_comul"
private theorem _root_.DieudonneFaithful.KerQuot.lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id k (B ⧸ kerIdeal d)) (counit d)).comp (comul d) =
      (Algebra.TensorProduct.rid k k (B ⧸ kerIdeal d)).symm := by
  refine Ideal.Quotient.algHom_ext k ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal d)).toLinearMap
      (counitAlgHom k B).toLinearMap
      = ((Ideal.Quotient.mkₐ k (kerIdeal d)).toLinearMap.rTensor k) ∘ₗ
          ((counitAlgHom k B).toLinearMap.lTensor B) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom k B).toLinearMap.lTensor B) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

p2m_export "DieudonneFaithful.KerQuot" "lTensor_counit_comul"

private theorem assoc_map_map_apply {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra k A']
    [Algebra k B'] (f : A' →ₐ[k] B') (z : (A' ⊗[k] A') ⊗[k] A') :
    (Algebra.TensorProduct.assoc k k k B' B' B')
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)
        (Algebra.TensorProduct.assoc k k k A' A' A' z) := by
  induction z with
  | zero => simp
  | tmul xy c =>
    induction xy with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coassoc :
    (Algebra.TensorProduct.assoc k k k (B ⧸ kerIdeal d) (B ⧸ kerIdeal d) (B ⧸ kerIdeal d)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul d) (.id k (B ⧸ kerIdeal d))).comp (comul d)) =
      (Algebra.TensorProduct.map (.id k (B ⧸ kerIdeal d)) (comul d)).comp (comul d) := by
  refine Ideal.Quotient.algHom_ext k ?_
  refine AlgHom.ext fun x => ?_
  set π := Ideal.Quotient.mkₐ k (kerIdeal d)
  have hL : ∀ z : B ⊗[k] B,
      Algebra.TensorProduct.map (comul d) (.id k (B ⧸ kerIdeal d)) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map (comulAlgHom k B) (.id k B) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : B ⊗[k] B,
      Algebra.TensorProduct.map (.id k (B ⧸ kerIdeal d)) (comul d) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id k B) (comulAlgHom k B) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul d (π x) = Algebra.TensorProduct.map π π (comulAlgHom k B x) := by
    simp [π, Ideal.Quotient.mkₐ_eq_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_algHom, hx, hL, hR, assoc_map_map_apply]
  congr 1
  have hassoc : ∀ z : (B ⊗[k] B) ⊗[k] B,
      Algebra.TensorProduct.assoc k k k B B B z = TensorProduct.assoc k B B B z := by
    intro z
    induction z with
    | zero => simp
    | tmul xy c =>
      induction xy with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [map_apply_eq_linearMap, map_apply_eq_linearMap, hassoc]
  exact Coalgebra.coassoc_apply x

noncomputable scoped instance instBialgebra : Bialgebra k (B ⧸ kerIdeal d) :=
  Bialgebra.ofAlgHom (comul d) (counit d) (coassoc d) (rTensor_counit_comul d)
    (lTensor_counit_comul d)

theorem coalgebra_comul_mk (x : B) :
    Coalgebra.comul (R := k) (Ideal.Quotient.mk (kerIdeal d) x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal d)) (Ideal.Quotient.mkₐ k (kerIdeal d))
        (Coalgebra.comul (R := k) x) := rfl

theorem coalgebra_counit_mk (x : B) :
    Coalgebra.counit (R := k) (Ideal.Quotient.mk (kerIdeal d) x) = Coalgebra.counit (R := k) x := rfl

scoped instance instIsCocomm [Coalgebra.IsCocomm k B] : Coalgebra.IsCocomm k (B ⧸ kerIdeal d) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.comp_apply, coalgebra_comul_mk]
    conv_rhs => rw [← Coalgebra.comm_comp_comul k B]
    rw [LinearMap.comp_apply]
    generalize Coalgebra.comul (R := k) x = z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]

noncomputable def proj : B →ₐc[k] B ⧸ kerIdeal d :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ k (kerIdeal d)) (counit_comp_mkₐ d) (comul_comp_mkₐ d).symm

@[scoped simp] theorem proj_apply (x : B) : proj d x = Ideal.Quotient.mk (kerIdeal d) x := rfl

theorem proj_surjective : Surjective (proj d) := Ideal.Quotient.mk_surjective

theorem iota_proj (x : B) : iota d (proj d x) = d x := iota_mk d x

theorem iota_comp_proj : (iota d).toRingHom.comp (proj d : B →ₐ[k] B ⧸ kerIdeal d).toRingHom =
    (d : B →ₐ[k] A).toRingHom :=
  RingHom.ext fun x => iota_mk d x

scoped instance instModuleFinite [Module.Finite k B] : Module.Finite k (B ⧸ kerIdeal d) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (kerIdeal d)).toLinearMap
    Ideal.Quotient.mk_surjective

end KerQuot
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual.DieudonneFaithful.KerQuot"

section Saturation

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Bialgebra k B]
  [Coalgebra.IsCocomm k B]

lemma mem_maximalIdeal_of_apply_one_eq_zero
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

lemma toConv_toDual_pow (φ : CartierDual k B) :
    ∀ m : ℕ, toConv (CartierDual.toDual k B (φ ^ m)) = (toConv (CartierDual.toDual k B φ)) ^ m
  | 0 => by
    rw [pow_zero, pow_zero]
    apply WithConv.ext
    rw [ofConv_toConv, CartierDual.convOne_ofConv_eq_counit]
    rfl
  | m + 1 => by
    rw [pow_succ, pow_succ, ← toConv_toDual_pow φ m, CartierDual.toDual_mul, toConv_ofConv]

variable [Module.Finite k B]

lemma isNilpotent_maximalIdeal (hloc : IsLocalRing (CartierDual k B)) :
    IsNilpotent (IsLocalRing.maximalIdeal (CartierDual k B)) := by
  haveI := hloc
  haveI : IsArtinianRing (CartierDual k B) := IsArtinianRing.of_finite k (CartierDual k B)
  have h := IsArtinianRing.isNilpotent_jacobson_bot (R := CartierDual k B)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h

lemma exists_forall_convPow_eq_zero (p : ℕ) [Fact p.Prime] (hloc : IsLocalRing (CartierDual k B)) :
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

end Saturation
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual.DieudonneFaithful.KerQuot"

section LengthOne

open Deformation

variable {k : Type*} [CommRing k] {p : ℕ} [Fact p.Prime]
  {Q : Type*} [CommRing Q] [Bialgebra k Q]

lemma mk_mem_wittHom_one {b : Q} (hb : Coalgebra.comul (R := k) b = b ⊗ₜ[k] 1 + 1 ⊗ₜ[k] b) :
    TruncatedWittVector.mk p (fun _ : Fin 1 => b) ∈ wittHom k p 1 Q := by
  rw [mem_wittHom_iff]
  refine TruncatedWittVector.ext fun i => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  rw [DieudonneModule.Examples.coeff_zero_add_of_length_one, TruncWitt.coeff_map,
    TruncWitt.coeff_map, TruncWitt.coeff_map, TruncatedWittVector.coeff_mk]
  change Coalgebra.comul (R := k) b = _
  rw [hb]
  rfl

end LengthOne
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual.DieudonneFaithful.KerQuot"

section Difference

open Deformation

variable {k : Type*} [Field k] {p : ℕ} [Fact p.Prime]
  {B : Type*} [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B]
  {A : Type*} [CommRing A] [Bialgebra k A]

noncomputable def diff (g g' : B →ₐc[k] A) : B →ₐc[k] A :=
  (toConv g * toConv (g'.comp (antipodeBialgHom k B))).ofConv

theorem diff_toAlgHom (g g' : B →ₐc[k] A) :
    (diff g g' : B →ₐ[k] A) =
      (toConv (g : B →ₐ[k] A) * toConv ((g' : B →ₐ[k] A).comp (antipodeAlgHom k B))).ofConv := by
  have := BialgHom.toAlgHom_convMul (toConv g) (toConv (g'.comp (antipodeBialgHom k B)))
  exact congrArg WithConv.ofConv this

theorem map_diff_eq_zero {g g' : B →ₐc[k] A}
    (h : DieudonneModule.map k p g = DieudonneModule.map k p g') {n : ℕ} (x : wittHom k p n B) :
    TruncWitt.map (diff g g' : B →ₐ[k] A).toRingHom (x : TruncatedWittVector p n B) = 0 := by
  have hlevel : wittHomMap p n g x = wittHomMap p n g' x := by
    apply DieudonneModule.of_injective n
    rw [← DieudonneModule.map_of, ← DieudonneModule.map_of, h]
  have hcoe := congrArg (fun y : wittHom k p n A => (y : TruncatedWittVector p n A)) hlevel
  simp only [coe_wittHomMap] at hcoe
  rw [diff_toAlgHom]
  rw [map_convMul_comp_antipode_of_mem_wittHom x.2, sub_eq_zero]
  exact hcoe

end Difference
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual.DieudonneFaithful.KerQuot"

end DieudonneFaithful
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual.DieudonneFaithful.KerQuot P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual.DieudonneFaithful"

universe u v w

open DieudonneFaithful Deformation WithConv in
theorem solution
    (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A]
    (B : Type w) [CommRing B] [HopfAlgebra k B] [Coalgebra.IsCocomm k B] [Module.Finite k B]
    (hB : IsLocalRing (CartierDual k B))
    (g g' : B →ₐc[k] A)
    (h : Deformation.DieudonneModule.map k p g = Deformation.DieudonneModule.map k p g') :
    g = g' := by
  classical
  set d : B →ₐc[k] A := diff g g' with hd

  have hQ : IsLocalRing (CartierDual k (B ⧸ KerQuot.kerIdeal d)) :=
    HopfAlgebra.isLocalRing_cartierDual_of_surjective k B (B ⧸ KerQuot.kerIdeal d)
      (KerQuot.proj d) (KerQuot.proj_surjective d) hB

  have hrank : Module.finrank k (B ⧸ KerQuot.kerIdeal d) = 1 := by
    by_contra hne
    obtain ⟨b, hb0, hb⟩ :=
      HopfAlgebra.exists_ne_zero_comul_eq_tmul_one_add_one_tmul_of_isLocalRing_cartierDual k
        (B ⧸ KerQuot.kerIdeal d) hQ hne

    obtain ⟨N, hN⟩ := exists_forall_convPow_eq_zero (k := k) (B := B) p hB
    have hV : ∀ β : WithConv (B →ₗ[k] k), β.ofConv 1 = 0 → β ^ p ^ (N + 1) = 0 := fun β hβ => by
      rw [pow_succ, pow_mul, hN β hβ, zero_pow (Fact.out : p.Prime).ne_zero]
    have hsurj : Surjective (wittHomMap p (N + 1) (KerQuot.proj d)) :=
      HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero k p (N + 1) B
        (B ⧸ KerQuot.kerIdeal d) (KerQuot.proj d) (KerQuot.proj_surjective d) hV

    set xb : wittHom k p 1 (B ⧸ KerQuot.kerIdeal d) :=
      ⟨TruncatedWittVector.mk p (fun _ : Fin 1 => b), mk_mem_wittHom_one hb⟩ with hxb
    have h1N : 1 ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    obtain ⟨x, hx⟩ := hsurj (wittHomShiftLE k p (B ⧸ KerQuot.kerIdeal d) h1N xb)

    have hπx : (wittHomMap p (N + 1) (KerQuot.proj d) x :
        TruncatedWittVector p (N + 1) (B ⧸ KerQuot.kerIdeal d)) = 0 := by
      apply TruncWitt.map_injective (KerQuot.iota_injective d)
      rw [map_zero, coe_wittHomMap, TruncWitt.map_map, KerQuot.iota_comp_proj]
      exact map_diff_eq_zero h x
    have hshift : wittHomShiftLE k p (B ⧸ KerQuot.kerIdeal d) h1N xb = 0 := by
      apply Subtype.ext
      rw [← hx, hπx]
      rfl
    have hxb0 : xb = 0 := wittHomShiftLE_injective h1N (by rw [hshift, map_zero])
    apply hb0
    have := congrArg (fun y : wittHom k p 1 (B ⧸ KerQuot.kerIdeal d) =>
      (y : TruncatedWittVector p 1 (B ⧸ KerQuot.kerIdeal d)).coeff 0) hxb0
    simpa [hxb] using this

  haveI : Nontrivial (B ⧸ KerQuot.kerIdeal d) := ⟨⟨0, 1, fun h0 => zero_ne_one (α := k)
    (by simpa using congrArg (Coalgebra.counit (R := k) (A := B ⧸ KerQuot.kerIdeal d)) h0)⟩⟩
  have hone : ∀ q : B ⧸ KerQuot.kerIdeal d, ∃ c : k, c • (1 : B ⧸ KerQuot.kerIdeal d) = q :=
    (finrank_eq_one_iff_of_nonzero' (1 : B ⧸ KerQuot.kerIdeal d) one_ne_zero).1 hrank
  have hdb : ∀ b : B, d b = algebraMap k A (Coalgebra.counit (R := k) b) := by
    intro b
    obtain ⟨c, hc⟩ := hone (Ideal.Quotient.mk (KerQuot.kerIdeal d) b)
    have hc' : Coalgebra.counit (R := k) b = c := by
      have := congrArg (KerQuot.counit d) hc
      rw [map_smul, map_one, smul_eq_mul, mul_one, KerQuot.counit_mk] at this
      exact this.symm
    have hmem : b - algebraMap k B c ∈ KerQuot.kerIdeal d := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hc, Ideal.Quotient.mk_algebraMap,
        Algebra.algebraMap_eq_smul_one, sub_self]
    have hd0 : d (b - algebraMap k B c) = 0 := hmem
    rw [map_sub, sub_eq_zero, AlgHomClass.commutes] at hd0
    rw [hd0, hc']
  have hd1 : toConv (g : B →ₐ[k] A) * toConv ((g' : B →ₐ[k] A).comp (antipodeAlgHom k B)) = 1 := by
    have e : (toConv (g : B →ₐ[k] A) * toConv ((g' : B →ₐ[k] A).comp (antipodeAlgHom k B))).ofConv =
        (1 : WithConv (B →ₐ[k] A)).ofConv := by
      rw [← diff_toAlgHom]
      refine AlgHom.ext fun b => ?_
      rw [AlgHom.convOne_apply]
      exact hdb b
    exact WithConv.ext e

  have hgg : toConv (g : B →ₐ[k] A) = toConv (g' : B →ₐ[k] A) := by
    calc toConv (g : B →ₐ[k] A)
        = toConv (g : B →ₐ[k] A) * (toConv ((g' : B →ₐ[k] A).comp (antipodeAlgHom k B)) *
            toConv (g' : B →ₐ[k] A)) := by
          rw [show toConv ((g' : B →ₐ[k] A).comp (antipodeAlgHom k B)) =
              toConv ((toConv (g' : B →ₐ[k] A)).ofConv.comp (antipodeAlgHom k B)) from rfl,
            comp_antipode_mul_point, mul_one]
      _ = toConv (g' : B →ₐ[k] A) := by rw [← mul_assoc, hd1, one_mul]
  exact BialgHom.coe_algHom_injective (toConv_injective hgg)

end S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_eq_of_map_eq_of_isLocalRing_cartierDual (solution)
