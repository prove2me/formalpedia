-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_ringHom_moduleEnd_forall_eq_pushPt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/8b04df91-24c7-5c2b-ba8c-88b2e267b4fc

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_CerednikDrinfeld_QM_existsUnique_linearMap_forall_eq_pushPt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct

theorem solution
    {κ : Type} [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ fX)
    (W : Type) [AddCommGroup W] [Module κ W]
    (τW : W → SchemeHomOver (tangentBase κ (RingHom.id κ)) fX)
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase κ (RingHom.id κ)) fX, P ∈ Set.range τW ↔ IsTangentVector L κ (RingHom.id κ) P)
    (hWadd : ∀ v w : W, τW (v + w) = L.mul (tangentBase κ (RingHom.id κ)) (τW v) (τW w))
    (hWsmul : ∀ (a : κ) (v : W), (τW (a • v)).1 = tangentScale κ a ≫ (τW v).1)
    {Λ : Type} [Ring Λ] (ψ : Λ → (X ⟶ X)) (hψ : ∀ x : Λ, ψ x ≫ fX = fX)
    (hψhom : ∀ (x : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P Q : SchemeHomOver t fX),
      pushPt (ψ x) (hψ x) (L.mul t P Q) = L.mul t (pushPt (ψ x) (hψ x) P) (pushPt (ψ x) (hψ x) Q))
    (hψone : ψ 1 = 𝟙 X) (hψmul : ∀ x y : Λ, ψ (x * y) = ψ y ≫ ψ x)
    (hψadd : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P : SchemeHomOver t fX),
      P.1 ≫ ψ (x + y) = (L.mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψ, P.2]⟩ ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψ, P.2]⟩).1) :
    ∃ θΛ : Λ →+* Module.End κ W, ∀ (x : Λ) (w : W), τW (θΛ x w) = pushPt (ψ x) (hψ x) (τW w) := by
  classical
  have hex : ∀ x : Λ, ∃ Φ : W →ₗ[κ] W, ∀ v : W, τW (Φ v) = pushPt (ψ x) (hψ x) (τW v) := fun x =>
    (CerednikDrinfeld.QM.existsUnique_linearMap_forall_eq_pushPt L κ (RingHom.id κ) W τW hWinj hWrange hWadd hWsmul
      (ψ x) (hψ x) (hψhom x)).exists
  choose Θ hΘ using hex
  have hone : Θ 1 = 1 := by
    apply LinearMap.ext; intro v
    apply hWinj
    rw [hΘ]
    apply Subtype.ext
    show (τW v).1 ≫ ψ 1 = (τW v).1
    rw [hψone, Category.comp_id]
  have hmul : ∀ x y, Θ (x * y) = Θ x * Θ y := by
    intro x y
    apply LinearMap.ext; intro v
    apply hWinj
    rw [hΘ, Module.End.mul_apply, hΘ, hΘ]
    apply Subtype.ext
    show (τW v).1 ≫ ψ (x * y) = ((τW v).1 ≫ ψ y) ≫ ψ x
    rw [hψmul, Category.assoc]
  have haddΘ : ∀ x y, Θ (x + y) = Θ x + Θ y := by
    intro x y
    apply LinearMap.ext; intro v
    apply hWinj
    rw [hΘ, LinearMap.add_apply, hWadd, hΘ, hΘ]
    apply Subtype.ext
    show (τW v).1 ≫ ψ (x + y) = _
    rw [hψadd x y (tangentBase κ (RingHom.id κ)) (τW v)]
    rfl
  have hzero : Θ 0 = 0 := by
    have h := haddΘ 0 0
    rw [add_zero] at h
    have h2 : Θ 0 + Θ 0 = Θ 0 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  exact ⟨{ toFun := Θ, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := haddΘ }, fun x w => hΘ x w⟩

end S_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_ringHom_moduleEnd_forall_eq_pushPt (solution)
