-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_addEquiv_prod_apply_eq_map_of_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/86ad19d6-4fa1-53d2-b73b-67b56629eafc

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct

open scoped TensorProduct

universe v

set_option autoImplicit false

universe u

namespace Deformation
p2m_export "Deformation" "TruncWitt.map wittHom map_convMul_of_mem_wittHom counit_coeff_of_mem_wittHom wittHomMap coe_wittHomMap DieudonneModule DieudonneModule.induction_on DieudonneModule.verschiebung DieudonneModule.frobenius DieudonneModule.map"
namespace DieudonneModule
p2m_export "Deformation.DieudonneModule" "of induction_on verschiebung frobenius map map_of map_verschiebung map_frobenius map_id map_comp"
namespace S4a
p2m_open "Deformation.DieudonneModule Deformation"

p2m_open "Deformation P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation Deformation.DieudonneModule P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation.DieudonneModule"

section Maps

variable (R : Type u) [CommRing R] (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂]
  [Bialgebra R B₁] [Bialgebra R B₂]

noncomputable def incl₁ : B₁ →ₐc[R] B₁ ⊗[R] B₂ :=
  (Bialgebra.TensorProduct.map (BialgHom.id R B₁) (Bialgebra.unitBialgHom R B₂)).comp
    ((Bialgebra.TensorProduct.rid R R B₁).symm : B₁ →ₐc[R] B₁ ⊗[R] R)

noncomputable def incl₂ : B₂ →ₐc[R] B₁ ⊗[R] B₂ :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom R B₁) (BialgHom.id R B₂)).comp
    ((Bialgebra.TensorProduct.lid R B₂).symm : B₂ →ₐc[R] R ⊗[R] B₂)

noncomputable def proj₁ : B₁ ⊗[R] B₂ →ₐc[R] B₁ :=
  ((Bialgebra.TensorProduct.rid R R B₁ : B₁ ⊗[R] R →ₐc[R] B₁)).comp
    (Bialgebra.TensorProduct.map (BialgHom.id R B₁) (Bialgebra.counitBialgHom R B₂))

noncomputable def proj₂ : B₁ ⊗[R] B₂ →ₐc[R] B₂ :=
  ((Bialgebra.TensorProduct.lid R B₂ : R ⊗[R] B₂ →ₐc[R] B₂)).comp
    (Bialgebra.TensorProduct.map (Bialgebra.counitBialgHom R B₁) (BialgHom.id R B₂))

variable {R B₁ B₂}

@[scoped simp] theorem incl₁_apply (x : B₁) : incl₁ R B₁ B₂ x = x ⊗ₜ[R] 1 := by
  simp [incl₁]

@[scoped simp] theorem incl₂_apply (y : B₂) : incl₂ R B₁ B₂ y = 1 ⊗ₜ[R] y := by
  simp [incl₂]

@[scoped simp] theorem proj₁_tmul (x : B₁) (y : B₂) :
    proj₁ R B₁ B₂ (x ⊗ₜ[R] y) = Coalgebra.counit (R := R) y • x := by
  simp [proj₁]

@[scoped simp] theorem proj₂_tmul (x : B₁) (y : B₂) :
    proj₂ R B₁ B₂ (x ⊗ₜ[R] y) = Coalgebra.counit (R := R) x • y := by
  simp [proj₂]

theorem incl₁_toAlgHom :
    (incl₁ R B₁ B₂ : B₁ →ₐ[R] B₁ ⊗[R] B₂) = Algebra.TensorProduct.includeLeft :=
  AlgHom.ext fun x => by simp

theorem incl₂_toAlgHom :
    (incl₂ R B₁ B₂ : B₂ →ₐ[R] B₁ ⊗[R] B₂) = Algebra.TensorProduct.includeRight :=
  AlgHom.ext fun x => by simp

theorem toLinearMap_incl₁_comp_proj₁ :
    ((incl₁ R B₁ B₂ : B₁ →ₐ[R] B₁ ⊗[R] B₂).comp (proj₁ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₁)).toLinearMap =
      TensorProduct.map (WithConv.toConv (LinearMap.id : B₁ →ₗ[R] B₁)).ofConv
        (1 : WithConv (B₂ →ₗ[R] B₂)).ofConv := by
  refine TensorProduct.ext' fun x y => ?_
  simp [LinearMap.convOne_apply, Algebra.algebraMap_eq_smul_one]

theorem toLinearMap_incl₂_comp_proj₂ :
    ((incl₂ R B₁ B₂ : B₂ →ₐ[R] B₁ ⊗[R] B₂).comp (proj₂ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₂)).toLinearMap =
      TensorProduct.map (1 : WithConv (B₁ →ₗ[R] B₁)).ofConv
        (WithConv.toConv (LinearMap.id : B₂ →ₗ[R] B₂)).ofConv := by
  refine TensorProduct.ext' fun x y => ?_
  simp [LinearMap.convOne_apply, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    Algebra.algebraMap_eq_smul_one]

theorem convMul_ofConv_eq_id :
    (WithConv.toConv ((incl₁ R B₁ B₂ : B₁ →ₐ[R] B₁ ⊗[R] B₂).comp
        (proj₁ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₁)) *
      WithConv.toConv ((incl₂ R B₁ B₂ : B₂ →ₐ[R] B₁ ⊗[R] B₂).comp
        (proj₂ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₂))).ofConv = AlgHom.id R (B₁ ⊗[R] B₂) := by
  apply AlgHom.toLinearMap_injective
  have h1 := AlgHom.toLinearMap_convMul
    (WithConv.toConv ((incl₁ R B₁ B₂ : B₁ →ₐ[R] B₁ ⊗[R] B₂).comp
        (proj₁ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₁)))
    (WithConv.toConv ((incl₂ R B₁ B₂ : B₂ →ₐ[R] B₁ ⊗[R] B₂).comp
        (proj₂ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₂)))
  have h2 := congrArg WithConv.ofConv h1
  rw [WithConv.ofConv_toConv] at h2
  rw [h2, WithConv.ofConv_toConv, WithConv.ofConv_toConv, toLinearMap_incl₁_comp_proj₁,
    toLinearMap_incl₂_comp_proj₂, TensorProduct.map_convMul_map, mul_one, one_mul,
    WithConv.ofConv_toConv, WithConv.ofConv_toConv, TensorProduct.map_id, AlgHom.toLinearMap_id]

end Maps

section Dieudonne

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {B₁ B₂ : Type v} [CommRing B₁] [CommRing B₂]
  [Bialgebra R B₁] [Bialgebra R B₂]

theorem wittHomMap_incl₁_proj₁_add {n : ℕ} (y : wittHom R p n (B₁ ⊗[R] B₂)) :
    wittHomMap p n ((incl₁ R B₁ B₂).comp (proj₁ R B₁ B₂)) y +
      wittHomMap p n ((incl₂ R B₁ B₂).comp (proj₂ R B₁ B₂)) y = y := by
  have key := map_convMul_of_mem_wittHom (T := B₁ ⊗[R] B₂) y.2
    (WithConv.toConv ((incl₁ R B₁ B₂ : B₁ →ₐ[R] B₁ ⊗[R] B₂).comp
        (proj₁ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₁)))
    (WithConv.toConv ((incl₂ R B₁ B₂ : B₂ →ₐ[R] B₁ ⊗[R] B₂).comp
        (proj₂ R B₁ B₂ : B₁ ⊗[R] B₂ →ₐ[R] B₂)))
  have hid : TruncWitt.map (AlgHom.id R (B₁ ⊗[R] B₂)).toRingHom
      (y : TruncatedWittVector p n (B₁ ⊗[R] B₂)) = y :=
    TruncatedWittVector.ext fun i => by simp
  rw [convMul_ofConv_eq_id, WithConv.ofConv_toConv, WithConv.ofConv_toConv, hid] at key
  apply Subtype.ext
  rw [AddSubgroup.coe_add, coe_wittHomMap, coe_wittHomMap]
  exact key.symm

theorem map_incl₁_proj₁_add (z : DieudonneModule R p (B₁ ⊗[R] B₂)) :
    map R p (incl₁ R B₁ B₂) (map R p (proj₁ R B₁ B₂) z) +
      map R p (incl₂ R B₁ B₂) (map R p (proj₂ R B₁ B₂) z) = z := by
  rw [← map_comp, ← map_comp]
  induction z using DieudonneModule.induction_on with
  | ih n y => rw [map_of, map_of, ← map_add, wittHomMap_incl₁_proj₁_add]

theorem map_proj₁_incl₁ (m : DieudonneModule R p B₁) :
    map R p (proj₁ R B₁ B₂) (map R p (incl₁ R B₁ B₂) m) = m := by
  induction m using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of, map_of]
    congr 1
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    simp

theorem map_proj₂_incl₂ (m : DieudonneModule R p B₂) :
    map R p (proj₂ R B₁ B₂) (map R p (incl₂ R B₁ B₂) m) = m := by
  induction m using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of, map_of]
    congr 1
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    simp

theorem map_proj₁_incl₂ (m : DieudonneModule R p B₂) :
    map R p (proj₁ R B₁ B₂) (map R p (incl₂ R B₁ B₂) m) = 0 := by
  induction m using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of, map_of, ← map_zero (of R p B₁ n)]
    congr 1
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    simp [counit_coeff_of_mem_wittHom x.2 i]

theorem map_proj₂_incl₁ (m : DieudonneModule R p B₁) :
    map R p (proj₂ R B₁ B₂) (map R p (incl₁ R B₁ B₂) m) = 0 := by
  induction m using DieudonneModule.induction_on with
  | ih n x =>
    rw [map_of, map_of, ← map_zero (of R p B₂ n)]
    congr 1
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    simp [counit_coeff_of_mem_wittHom x.2 i]

variable (R p B₁ B₂) in

noncomputable def prodEquiv :
    DieudonneModule R p (B₁ ⊗[R] B₂) ≃+ DieudonneModule R p B₁ × DieudonneModule R p B₂ :=
  AddMonoidHom.toAddEquiv
    ((map R p (proj₁ R B₁ B₂)).prod (map R p (proj₂ R B₁ B₂)))
    ((map R p (incl₁ R B₁ B₂)).coprod (map R p (incl₂ R B₁ B₂)))
    (AddMonoidHom.ext fun z => by simp [map_incl₁_proj₁_add])
    (AddMonoidHom.ext fun m => by
      obtain ⟨m₁, m₂⟩ := m
      simp [map_proj₁_incl₁, map_proj₂_incl₂, map_proj₁_incl₂, map_proj₂_incl₁])

@[scoped simp] theorem prodEquiv_apply (z : DieudonneModule R p (B₁ ⊗[R] B₂)) :
    prodEquiv R p B₁ B₂ z = (map R p (proj₁ R B₁ B₂) z, map R p (proj₂ R B₁ B₂) z) := rfl

@[scoped simp] theorem prodEquiv_symm_apply (m₁ : DieudonneModule R p B₁) (m₂ : DieudonneModule R p B₂) :
    (prodEquiv R p B₁ B₂).symm (m₁, m₂) =
      map R p (incl₁ R B₁ B₂) m₁ + map R p (incl₂ R B₁ B₂) m₂ := rfl

theorem prodEquiv_frobenius [CharP R p] (z : DieudonneModule R p (B₁ ⊗[R] B₂)) :
    prodEquiv R p B₁ B₂ (frobenius R p (B₁ ⊗[R] B₂) z) =
      (frobenius R p B₁ (prodEquiv R p B₁ B₂ z).1, frobenius R p B₂ (prodEquiv R p B₁ B₂ z).2) := by
  simp [map_frobenius]

theorem prodEquiv_verschiebung (z : DieudonneModule R p (B₁ ⊗[R] B₂)) :
    prodEquiv R p B₁ B₂ (verschiebung R p (B₁ ⊗[R] B₂) z) =
      (verschiebung R p B₁ (prodEquiv R p B₁ B₂ z).1,
        verschiebung R p B₂ (prodEquiv R p B₁ B₂ z).2) := by
  simp [map_verschiebung]

end Dieudonne

end Deformation.DieudonneModule.S4a
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation.DieudonneModule P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation.DieudonneModule.S4a"
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation.DieudonneModule"
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct.Deformation"

theorem solution
    (p : ℕ) [Fact p.Prime]
    (B₁ B₂ : Type v) [CommRing B₁] [CommRing B₂] [Bialgebra (ZMod p) B₁] [Bialgebra (ZMod p) B₂] :
    ∃ (i₁ : B₁ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂) (i₂ : B₂ →ₐc[ZMod p] B₁ ⊗[ZMod p] B₂)
      (q₁ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₁) (q₂ : B₁ ⊗[ZMod p] B₂ →ₐc[ZMod p] B₂),
      (i₁ : B₁ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeLeft ∧
      (i₂ : B₂ →ₐ[ZMod p] B₁ ⊗[ZMod p] B₂) = Algebra.TensorProduct.includeRight ∧
      (∀ x y, q₁ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) y • x) ∧
      (∀ x y, q₂ (x ⊗ₜ[ZMod p] y) = Coalgebra.counit (R := ZMod p) x • y) ∧
      ∃ e : Deformation.DieudonneModule (ZMod p) p (B₁ ⊗[ZMod p] B₂) ≃+
          Deformation.DieudonneModule (ZMod p) p B₁ × Deformation.DieudonneModule (ZMod p) p B₂,
        (∀ z, e z = (Deformation.DieudonneModule.map (ZMod p) p q₁ z,
          Deformation.DieudonneModule.map (ZMod p) p q₂ z)) ∧
        (∀ m₁ m₂, e.symm (m₁, m₂) = Deformation.DieudonneModule.map (ZMod p) p i₁ m₁ +
          Deformation.DieudonneModule.map (ZMod p) p i₂ m₂) ∧
        (∀ z, e (Deformation.DieudonneModule.frobenius (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.frobenius (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.frobenius (ZMod p) p B₂ (e z).2)) ∧
        (∀ z, e (Deformation.DieudonneModule.verschiebung (ZMod p) p (B₁ ⊗[ZMod p] B₂) z) =
          (Deformation.DieudonneModule.verschiebung (ZMod p) p B₁ (e z).1,
            Deformation.DieudonneModule.verschiebung (ZMod p) p B₂ (e z).2)) :=
  ⟨Deformation.DieudonneModule.S4a.incl₁ (ZMod p) B₁ B₂, Deformation.DieudonneModule.S4a.incl₂ (ZMod p) B₁ B₂,
    Deformation.DieudonneModule.S4a.proj₁ (ZMod p) B₁ B₂, Deformation.DieudonneModule.S4a.proj₂ (ZMod p) B₁ B₂,
    Deformation.DieudonneModule.S4a.incl₁_toAlgHom, Deformation.DieudonneModule.S4a.incl₂_toAlgHom,
    Deformation.DieudonneModule.S4a.proj₁_tmul, Deformation.DieudonneModule.S4a.proj₂_tmul,
    Deformation.DieudonneModule.S4a.prodEquiv (ZMod p) p B₁ B₂,
    Deformation.DieudonneModule.S4a.prodEquiv_apply, Deformation.DieudonneModule.S4a.prodEquiv_symm_apply,
    Deformation.DieudonneModule.S4a.prodEquiv_frobenius, Deformation.DieudonneModule.S4a.prodEquiv_verschiebung⟩

end S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_addEquiv_prod_apply_eq_map_of_tensorProduct (solution)
