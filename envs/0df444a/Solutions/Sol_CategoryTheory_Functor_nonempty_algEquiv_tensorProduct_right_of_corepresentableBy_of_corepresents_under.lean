-- Prove2me | solution 1 for CategoryTheory.Functor.nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2f9fbfe4-24f4-5fe8-a799-e7fb1e0603f1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace AffDescBridge

variable {R : Type u} [CommRing R]

abbrev objOf (D : Type u) [CommRing D] [Algebra R D] : Under (CommRingCat.of R) :=
  Under.mk (CommRingCat.ofHom (algebraMap R D))

abbrev homOf {D D' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (ψ : D →ₐ[R] D') :
    objOf (R := R) D ⟶ objOf D' :=
  Under.homMk (CommRingCat.ofHom ψ.toRingHom) (by ext r; exact ψ.commutes r)

lemma homOf_comp {D D' D'' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing D''] [Algebra R D'']
    (ψ : D →ₐ[R] D') (ψ' : D' →ₐ[R] D'') : homOf (ψ'.comp ψ) = homOf ψ ≫ homOf ψ' := by
  apply Under.UnderMorphism.ext; rfl

scoped instance instAlgebraRight (C₁ : Under (CommRingCat.of R)) : Algebra R (C₁.right : Type u) :=
  (show R →+* C₁.right from C₁.hom.hom).toAlgebra

variable (C₁ : Under (CommRingCat.of R))

lemma algebraMap_right_apply (r : R) : algebraMap R (C₁.right : Type u) r = C₁.hom.hom r := rfl

abbrev algOf {D : Type u} [CommRing D] [Algebra R D] (q : C₁ ⟶ objOf (R := R) D) : (C₁.right : Type u) →ₐ[R] D :=
  { toRingHom := (show (C₁.right : Type u) →+* D from q.right.hom),
    commutes' := fun r => congrArg (fun (k : CommRingCat.of R ⟶ CommRingCat.of D) => k.hom r) (Under.w q) }

abbrev homOfC {D : Type u} [CommRing D] [Algebra R D] (g : (C₁.right : Type u) →ₐ[R] D) : C₁ ⟶ objOf (R := R) D :=
  Under.homMk (CommRingCat.ofHom g.toRingHom) (by ext r; exact g.commutes r)

lemma algOf_homOfC {D : Type u} [CommRing D] [Algebra R D] (g : (C₁.right : Type u) →ₐ[R] D) :
    algOf C₁ (homOfC C₁ g) = g := AlgHom.ext fun _ => rfl

lemma homOfC_algOf {D : Type u} [CommRing D] [Algebra R D] (q : C₁ ⟶ objOf (R := R) D) :
    homOfC C₁ (algOf C₁ q) = q := by
  apply Under.UnderMorphism.ext; ext a; rfl

lemma algOf_comp {D D' : Type u} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    (q : C₁ ⟶ objOf (R := R) D) (ψ : D →ₐ[R] D') :
    algOf C₁ (q ≫ homOf ψ) = ψ.comp (algOf C₁ q) := AlgHom.ext fun _ => rfl

end AffDescBridge
p2m_reactivate "P2MW.S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under.AffDescBridge"

namespace AffD

variable {R : Type u} [CommRing R]

def underToAlg {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B))) :
    A →ₐ[R] B :=
  { toRingHom := (show A →+* B from k.right.hom)
    commutes' := fun r => congrArg (fun (q : CommRingCat.of R ⟶ CommRingCat.of B) => q.hom r) (Under.w k) }

def algToUnder {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B) :
    Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B)) :=
  Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext r; exact f.commutes r)

@[scoped simp] theorem underToAlg_apply {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B))) (a : A) :
    underToAlg k a = k.right.hom a := rfl

@[scoped simp] theorem algToUnder_right_hom {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (a : A) :
    (algToUnder f).right.hom a = f a := rfl

theorem algToUnder_underToAlg {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B))) :
    algToUnder (underToAlg k) = k :=
  Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

theorem underToAlg_algToUnder {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B) :
    underToAlg (algToUnder f) = f :=
  AlgHom.ext fun _ => rfl

theorem algToUnder_comp {A B D : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    (f : A →ₐ[R] B) (g : B →ₐ[R] D) :
    algToUnder (g.comp f) = algToUnder f ≫ algToUnder g :=
  Under.UnderMorphism.ext (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

theorem underToAlg_comp {A B D : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D]
    (k : Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B)))
    (g : Under.mk (CommRingCat.ofHom (algebraMap R B)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R D))) :
    underToAlg (k ≫ g) = (underToAlg g).comp (underToAlg k) :=
  AlgHom.ext fun _ => rfl

end AffD
p2m_reactivate "P2MW.S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under.AffDescBridge P2MW.S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under.AffD"

open AffDescBridge AffD in
theorem solution
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (C : Under (CommRingCat.of R)) (hC : F.CorepresentableBy C)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B'),
      F.obj B' ≃
        {g : Under.mk (CommRingCat.ofHom (algebraMap R C₁)) ⟶ B' //
          Under.homMk (U := Under.mk (CommRingCat.ofHom (algebraMap R S₁)))
              (V := Under.mk (CommRingCat.ofHom (algebraMap R C₁)))
              (CommRingCat.ofHom (algebraMap S₁ C₁)) (by ext r; exact (IsScalarTower.algebraMap_apply R S₁ C₁ r).symm) ≫ g = b})
    (he : ∀ (B' B'' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B')
      (ψ : B' ⟶ B'') (x : F.obj B'), ((e B'' (b ≫ ψ)) (F.map ψ x)).1 = ((e B' b) x).1 ≫ ψ) :
    letI : Algebra R C.right := C.hom.hom.toAlgebra
    Nonempty (S₁ ⊗[R] C.right ≃ₐ[S₁] C₁) := by
  classical
  letI instC : Algebra R (C.right : Type u) := AffDescBridge.instAlgebraRight C
  let Cr : Type u := C.right
  let T : Type u := S₁ ⊗[R] Cr
  let oS : Under (CommRingCat.of R) := objOf S₁
  let oC₁ : Under (CommRingCat.of R) := objOf C₁
  let oT : Under (CommRingCat.of R) := objOf T
  let c : oS ⟶ oC₁ := Under.homMk (U := oS) (V := oC₁) (CommRingCat.ofHom (algebraMap S₁ C₁))
    (by ext r; exact (IsScalarTower.algebraMap_apply R S₁ C₁ r).symm)
  let bT : oS ⟶ oT := Under.homMk (U := oS) (V := oT) (CommRingCat.ofHom (algebraMap S₁ T))
    (by ext r; exact (IsScalarTower.algebraMap_apply R S₁ T r).symm)

  let κ : C ⟶ oT := homOfC C (Algebra.TensorProduct.includeRight : Cr →ₐ[R] T)
  let x₀ : F.obj oT := hC.homEquiv κ
  let g₀ := e oT bT x₀
  let αu : oC₁ ⟶ oT := g₀.1
  have hαc : c ≫ αu = bT := g₀.2
  let α₀ : C₁ →ₐ[R] T := underToAlg αu
  have hαS : ∀ s : S₁, α₀ (algebraMap S₁ C₁ s) = algebraMap S₁ T s := fun s =>
    congrArg (fun (q : oS ⟶ oT) => q.right.hom s) hαc
  let α : C₁ →ₐ[S₁] T := { toRingHom := α₀.toRingHom, commutes' := hαS }
  let y₀ : F.obj oC₁ := (e oC₁ c).symm ⟨𝟙 oC₁, Category.comp_id c⟩
  have hy₀ : e oC₁ c y₀ = ⟨𝟙 oC₁, Category.comp_id c⟩ := Equiv.apply_symm_apply _ _
  let βu : C ⟶ oC₁ := hC.homEquiv.symm y₀
  have hβu : hC.homEquiv βu = y₀ := Equiv.apply_symm_apply _ _
  let β₀ : Cr →ₐ[R] C₁ := algOf C βu
  let β : T →ₐ[S₁] C₁ := Algebra.TensorProduct.lift (Algebra.ofId S₁ C₁) β₀ (fun _ _ => Commute.all _ _)
  have hβR : (β.restrictScalars R).comp (Algebra.TensorProduct.includeRight : Cr →ₐ[R] T) = β₀ :=
    Algebra.TensorProduct.lift_comp_includeRight _ _ (fun _ _ => Commute.all _ _)
  let βT : oT ⟶ oC₁ := algToUnder (β.restrictScalars R)
  have hβc : bT ≫ βT = c := by
    apply Under.UnderMorphism.ext; ext s
    change β (algebraMap S₁ T s) = algebraMap S₁ C₁ s
    exact β.commutes s
  have hκβ : κ ≫ βT = βu := by
    rw [← homOfC_algOf C βu]
    apply Under.UnderMorphism.ext; ext x
    exact DFunLike.congr_fun hβR x

  have h1 : αu ≫ βT = 𝟙 oC₁ := by
    have hnat := he oT oC₁ bT βT x₀
    rw [hβc] at hnat
    have hx : F.map βT x₀ = y₀ := by
      change F.map βT (hC.homEquiv κ) = y₀
      rw [← hC.homEquiv_comp βT κ, hκβ, hβu]
    rw [hx, hy₀] at hnat
    exact hnat.symm

  have hβα : βu ≫ αu = κ := by
    apply hC.homEquiv.injective
    rw [hC.homEquiv_comp αu βu, hβu]
    change F.map αu y₀ = x₀
    apply (e oT bT).injective
    apply Subtype.ext
    have hnat := he oC₁ oT c αu y₀
    rw [hαc] at hnat
    rw [hnat, hy₀]
    exact Category.id_comp αu
  refine ⟨AlgEquiv.ofAlgHom β α ?_ ?_⟩
  ·
    apply AlgHom.ext
    intro x
    exact congrArg (fun (q : oC₁ ⟶ oC₁) => q.right.hom x) h1
  ·
    apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro s
      change α (β (s ⊗ₜ[R] (1 : Cr))) = s ⊗ₜ[R] (1 : Cr)
      have hs : (s ⊗ₜ[R] (1 : Cr) : T) = algebraMap S₁ T s := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hs, AlgHom.commutes, AlgHom.commutes]
    · apply AlgHom.ext
      intro x
      change α (β ((Algebra.TensorProduct.includeRight : Cr →ₐ[R] T) x)) =
        (Algebra.TensorProduct.includeRight : Cr →ₐ[R] T) x
      rw [show β ((Algebra.TensorProduct.includeRight : Cr →ₐ[R] T) x) = β₀ x from DFunLike.congr_fun hβR x]
      exact congrArg (fun (q : C ⟶ oT) => q.right.hom x) hβα

end S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under
end P2MW
export P2MW.S_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under (solution)
