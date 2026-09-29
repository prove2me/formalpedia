-- Prove2me | solution 1 for CommRingCat.isPushout_tensorProduct_tensorProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1d333cdf-0de7-59fe-ad27-967b7cc90bc6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CommRingCat_isPushout_tensorProduct_tensorProduct

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

theorem solution
    (R : Type u) [CommRing R] (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] :
    IsPushout
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C)).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B ⊗[R] C →ₐ[R] A ⊗[R] (B ⊗[R] C)).toRingHom) := by
  classical
  letI : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower R B (A ⊗[R] B) := Algebra.TensorProduct.right_isScalarTower

  have h0 := CommRingCat.isPushout_tensorProduct B (A ⊗[R] B) (B ⊗[R] C)

  let e1 : (A ⊗[R] B) ⊗[B] (B ⊗[R] C) ≃ₐ[B] (A ⊗[R] B) ⊗[R] C :=
    Algebra.TensorProduct.cancelBaseChange R B B (A ⊗[R] B) C
  let e2 : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] A ⊗[R] (B ⊗[R] C) := Algebra.TensorProduct.assoc R R R A B C
  let e : (A ⊗[R] B) ⊗[B] (B ⊗[R] C) ≃+* A ⊗[R] (B ⊗[R] C) := e1.toRingEquiv.trans e2.toRingEquiv
  have he_left : ∀ (a : A) (b : B), e ((a ⊗ₜ[R] b) ⊗ₜ[B] (1 : B ⊗[R] C)) = a ⊗ₜ[R] (b ⊗ₜ[R] (1 : C)) := by
    intro a b
    show e2 (e1 ((a ⊗ₜ[R] b) ⊗ₜ[B] (1 : B ⊗[R] C))) = _
    rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul, Algebra.TensorProduct.assoc_tmul]
  have he_right : ∀ (b : B) (c : C), e ((1 : A ⊗[R] B) ⊗ₜ[B] (b ⊗ₜ[R] c)) = (1 : A) ⊗ₜ[R] (b ⊗ₜ[R] c) := by
    intro b c
    show e2 (e1 ((1 : A ⊗[R] B) ⊗ₜ[B] (b ⊗ₜ[R] c))) = _
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one,
      show algebraMap B (A ⊗[R] B) b = (1 : A) ⊗ₜ[R] b from rfl, Algebra.TensorProduct.assoc_tmul]
  refine IsPushout.of_iso h0 (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    show algebraMap B (B ⊗[R] C) b = b ⊗ₜ[R] (1 : C)
    rfl
  · simp only [Iso.refl_hom, Category.id_comp]
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    show e (Algebra.TensorProduct.includeLeftRingHom x) = Algebra.TensorProduct.map (AlgHom.id R A) Algebra.TensorProduct.includeLeft x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply]
      exact he_left a b
    | add x y hx hy =>
      rw [(Algebra.TensorProduct.includeLeftRingHom).map_add, e.map_add, hx, hy]
      exact (map_add (Algebra.TensorProduct.map (AlgHom.id R A) Algebra.TensorProduct.includeLeft) x y).symm
  · simp only [Iso.refl_hom, Category.id_comp]
    refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
    show e (Algebra.TensorProduct.includeRight x) = Algebra.TensorProduct.includeRight x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeRight_apply]
      exact he_right b c
    | add x y hx hy =>
      rw [map_add (Algebra.TensorProduct.includeRight (R := B) (A := A ⊗[R] B) (B := B ⊗[R] C)) x y, e.map_add, hx, hy,
        map_add (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B ⊗[R] C)) x y]

end S_CommRingCat_isPushout_tensorProduct_tensorProduct
end P2MW
export P2MW.S_CommRingCat_isPushout_tensorProduct_tensorProduct (solution)
