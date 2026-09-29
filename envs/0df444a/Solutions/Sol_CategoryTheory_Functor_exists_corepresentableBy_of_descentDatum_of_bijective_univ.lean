-- Prove2me | solution 1 for CategoryTheory.Functor.exists_corepresentableBy_of_descentDatum_of_bijective_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/96d4797e-a638-5365-aa6c-7c78fa7e94fe

import Mathlib
import Theorems.Thm_Module_FaithfullyFlat_exists_algebraMap_eq_of_tmul_one_eq_one_tmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

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

def homEquivAlg {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] :
    (Under.mk (CommRingCat.ofHom (algebraMap R A)) ⟶ Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃ (A →ₐ[R] B) where
  toFun := underToAlg
  invFun := algToUnder
  left_inv := algToUnder_underToAlg
  right_inv := underToAlg_algToUnder

section Alg

variable (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
  (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
  (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)

abbrev Cst : Subalgebra R C₁ :=
  AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁))
    (Algebra.TensorProduct.includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)

theorem mem_Cst (a : C₁) : a ∈ Cst S₁ C₁ φ ↔ φ (a ⊗ₜ[R] 1) = (1 : S₁) ⊗ₜ[R] a := by
  rw [Cst, AlgHom.mem_equalizer]; rfl

def ι₀ : S₁ ⊗[R] ↥(Cst S₁ C₁ φ) →ₐ[R] C₁ :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S₁ C₁) (Cst S₁ C₁ φ).val (fun s a => Commute.all _ _)

theorem ι₀_tmul (s : S₁) (a : ↥(Cst S₁ C₁ φ)) : ι₀ S₁ C₁ φ (s ⊗ₜ[R] a) = algebraMap S₁ C₁ s * (a : C₁) :=
  Algebra.TensorProduct.lift_tmul _ _ _ s a

variable {S₁ C₁ φ}

theorem algHom_ext_of_surjective (hsurj : Function.Surjective (ι₀ S₁ C₁ φ))
    {D : Type u} [Semiring D] [Algebra R D] {g₁ g₂ : C₁ →ₐ[R] D}
    (h₁ : ∀ s : S₁, g₁ (algebraMap S₁ C₁ s) = g₂ (algebraMap S₁ C₁ s))
    (h₂ : ∀ a : ↥(Cst S₁ C₁ φ), g₁ (a : C₁) = g₂ (a : C₁)) : g₁ = g₂ := by
  apply AlgHom.ext
  intro c
  obtain ⟨z, rfl⟩ := hsurj c
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s a => rw [ι₀_tmul, map_mul, map_mul, h₁, h₂]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

variable (B : Type u) [CommRing B] [Algebra R B]

theorem includeLeft_injective [Module.FaithfullyFlat R S₁] :
    Function.Injective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) := by
  intro x y hxy
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S₁) B
  have := congrArg (TensorProduct.comm R B S₁) hxy
  simpa [Algebra.TensorProduct.includeLeft_apply] using this

variable {B}

noncomputable def gOf (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) :
    C₁ →ₐ[R] B ⊗[R] S₁ :=
  (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)
      ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁).comp f) (fun _ _ => Commute.all _ _)).comp
    ((AlgEquiv.ofBijective (ι₀ S₁ C₁ φ) hbij).symm.toAlgHom)

theorem gOf_ι₀ (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) (z : S₁ ⊗[R] ↥(Cst S₁ C₁ φ)) :
    gOf hbij f (ι₀ S₁ C₁ φ z) =
      Algebra.TensorProduct.lift (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)
        ((Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁).comp f) (fun _ _ => Commute.all _ _) z := by
  unfold gOf
  rw [AlgHom.comp_apply]
  congr 1
  exact (AlgEquiv.ofBijective (ι₀ S₁ C₁ φ) hbij).symm_apply_apply z

theorem gOf_algebraMap (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) (s : S₁) :
    gOf hbij f (algebraMap S₁ C₁ s) = (1 : B) ⊗ₜ[R] s := by
  have : algebraMap S₁ C₁ s = ι₀ S₁ C₁ φ (s ⊗ₜ[R] 1) := by rw [ι₀_tmul]; simp
  rw [this, gOf_ι₀, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.TensorProduct.includeRight_apply]

theorem gOf_coe (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) (a : ↥(Cst S₁ C₁ φ)) :
    gOf hbij f (a : C₁) = f a ⊗ₜ[R] (1 : S₁) := by
  have : (a : C₁) = ι₀ S₁ C₁ φ (1 ⊗ₜ[R] a) := by rw [ι₀_tmul]; simp
  rw [this, gOf_ι₀, Algebra.TensorProduct.lift_tmul]
  simp [Algebra.TensorProduct.includeLeft_apply]

theorem gOf_comp_toAlgHom (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) :
    (gOf hbij f).comp (IsScalarTower.toAlgHom R S₁ C₁) = Algebra.TensorProduct.includeRight := by
  apply AlgHom.ext; intro s
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', gOf_algebraMap]
  rfl

theorem gOf_unique (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B)
    (g : C₁ →ₐ[R] B ⊗[R] S₁) (hg₁ : g.comp (IsScalarTower.toAlgHom R S₁ C₁) = Algebra.TensorProduct.includeRight)
    (hg₂ : ∀ a : ↥(Cst S₁ C₁ φ), g (a : C₁) = f a ⊗ₜ[R] (1 : S₁)) : g = gOf hbij f := by
  apply algHom_ext_of_surjective hbij.2
  · intro s
    rw [gOf_algebraMap]
    have := AlgHom.congr_fun hg₁ s
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]; rfl
  · intro a; rw [hg₂, gOf_coe]

noncomputable def fOf [Module.FaithfullyFlat R S₁] (g : C₁ →ₐ[R] B ⊗[R] S₁)
    (hg : ∀ a : ↥(Cst S₁ C₁ φ), g (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁)) :
    ↥(Cst S₁ C₁ φ) →ₐ[R] B :=
  ((AlgEquiv.ofInjective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) (includeLeft_injective B)).symm.toAlgHom).comp
    ((g.comp (Cst S₁ C₁ φ).val).codRestrict (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁).range
      (fun a => by obtain ⟨b, hb⟩ := hg a; exact ⟨b, hb⟩))

theorem includeLeft_fOf [Module.FaithfullyFlat R S₁] (g : C₁ →ₐ[R] B ⊗[R] S₁)
    (hg : ∀ a : ↥(Cst S₁ C₁ φ), g (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁))
    (a : ↥(Cst S₁ C₁ φ)) :
    (fOf g hg a) ⊗ₜ[R] (1 : S₁) = g (a : C₁) := by
  show (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) (fOf g hg a) = g a
  unfold fOf
  rw [AlgHom.comp_apply]
  have := AlgEquiv.ofInjective_apply (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) (includeLeft_injective B)
    ((AlgEquiv.ofInjective (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) (includeLeft_injective B)).symm
      (((g.comp (Cst S₁ C₁ φ).val).codRestrict (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁).range
        (fun a => by obtain ⟨b, hb⟩ := hg a; exact ⟨b, hb⟩)) a))
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

theorem fOf_gOf [Module.FaithfullyFlat R S₁] (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B)
    (hg : ∀ a : ↥(Cst S₁ C₁ φ), gOf hbij f (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁)) :
    fOf (gOf hbij f) hg = f := by
  apply AlgHom.ext; intro a
  apply includeLeft_injective (R := R) (S₁ := S₁) B
  show (fOf (gOf hbij f) hg a) ⊗ₜ[R] (1 : S₁) = f a ⊗ₜ[R] 1
  rw [includeLeft_fOf, gOf_coe]

end Alg

section Main

variable (F : Under (CommRingCat.of R) ⥤ Type v)
  (S₁ : Type u) [CommRing S₁] [Algebra R S₁] [Module.FaithfullyFlat R S₁]
  (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
  (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
  (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)

abbrev U (B : Type u) [CommRing B] [Algebra R B] : Under (CommRingCat.of R) := Under.mk (CommRingCat.ofHom (algebraMap R B))

noncomputable abbrev ιU (B : Type u) [CommRing B] [Algebra R B] : U (R := R) B ⟶ U (R := R) (B ⊗[R] S₁) :=
  algToUnder (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁)

theorem e_congr {D : Type u} [CommRing D] [Algebra R D] {j₁ j₂ : S₁ →ₐ[R] D} (h : j₁ = j₂)
    (x : F.obj (U (R := R) D)) : ((e D j₁ x).1 : C₁ →ₐ[R] D) = (e D j₂ x).1 := by
  subst h; rfl

variable {F S₁ C₁}

noncomputable def gPt {B : Type u} [CommRing B] [Algebra R B] (y : F.obj (U (R := R) (B ⊗[R] S₁))) : C₁ →ₐ[R] B ⊗[R] S₁ :=
  ((e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)) y).1

theorem gPt_comp {B : Type u} [CommRing B] [Algebra R B] (y : F.obj (U (R := R) (B ⊗[R] S₁))) :
    (gPt e y).comp (IsScalarTower.toAlgHom R S₁ C₁) = Algebra.TensorProduct.includeRight :=
  ((e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)) y).2

theorem descends_iff
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hsurj : Function.Surjective (ι₀ S₁ C₁ φ))
    {B : Type u} [CommRing B] [Algebra R B] (y : F.obj (U (R := R) (B ⊗[R] S₁))) :
    F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y = F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y ↔
      ∀ a : ↥(Cst S₁ C₁ φ), gPt e y (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁) := by
  classical

  set P := pushout (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) with hP
  letI instD : Algebra R (P.right : Type u) := (show R →+* P.right from P.hom.hom).toAlgebra
  have hPU : U (R := R) (P.right : Type u) = P := rfl
  let inlA : B ⊗[R] S₁ →ₐ[R] (P.right : Type u) := underToAlg (A := B ⊗[R] S₁) (B := (P.right : Type u)) (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B))
  let inrA : B ⊗[R] S₁ →ₐ[R] (P.right : Type u) := underToAlg (A := B ⊗[R] S₁) (B := (P.right : Type u)) (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B))
  have hinl : algToUnder inlA = pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) := algToUnder_underToAlg _
  have hinr : algToUnder inrA = pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) := algToUnder_underToAlg _

  have hcond : ∀ b : B, inlA (b ⊗ₜ[R] 1) = inrA (b ⊗ₜ[R] 1) := fun b =>
    congrArg (fun (k : U (R := R) B ⟶ P) => k.right.hom b) (pushout.condition (f := ιU (R := R) S₁ B) (g := ιU (R := R) S₁ B))

  let inR : S₁ →ₐ[R] B ⊗[R] S₁ := Algebra.TensorProduct.includeRight
  let d : S₁ ⊗[R] S₁ →ₐ[R] (P.right : Type u) :=
    Algebra.TensorProduct.lift (inlA.comp inR) (inrA.comp inR) (fun _ _ => Commute.all _ _)
  have hd₁ : d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁) = inlA.comp inR :=
    Algebra.TensorProduct.lift_comp_includeLeft _ _ _
  have hd₂ : d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁) = inrA.comp inR := by
    apply AlgHom.ext; intro s
    show d ((1 : S₁) ⊗ₜ[R] s) = inrA (inR s)
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, map_one, map_one, one_mul, AlgHom.comp_apply]

  have hgS : ∀ s : S₁, gPt e y (algebraMap S₁ C₁ s) = (1 : B) ⊗ₜ[R] s := by
    intro s
    have := AlgHom.congr_fun (gPt_comp e y) s
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom'] at this
    rw [this]; rfl

  have hinl' : Under.homMk (CommRingCat.ofHom inlA.toRingHom) (by ext r; exact inlA.commutes r) =
      pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) := hinl
  have hinr' : Under.homMk (CommRingCat.ofHom inrA.toRingHom) (by ext r; exact inrA.commutes r) =
      pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B) := hinr
  have he₁ : ((e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁)))
      (F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).1 = inlA.comp (gPt e y) := by
    rw [e_congr F S₁ C₁ e hd₁]
    have := he (B ⊗[R] S₁) (P.right : Type u) inR inlA y
    have hF : F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y =
        F.map (Under.homMk (CommRingCat.ofHom inlA.toRingHom) (by ext r; exact inlA.commutes r)) y :=
      congrArg (fun k => F.map k y) hinl'.symm
    rw [hF]; exact this
  have he₂ : ((e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁)))
      (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).1 = inrA.comp (gPt e y) := by
    rw [e_congr F S₁ C₁ e hd₂]
    have := he (B ⊗[R] S₁) (P.right : Type u) inR inrA y
    have hF : F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y =
        F.map (Under.homMk (CommRingCat.ofHom inrA.toRingHom) (by ext r; exact inrA.commutes r)) y :=
      congrArg (fun k => F.map k y) hinr'.symm
    rw [hF]; exact this

  have hstar := hφ (P.right : Type u) d (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)
  rw [he₂] at hstar
  set G : C₁ →ₐ[R] (P.right : Type u) := ((e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁)))
      (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).1 with hG
  have hGS : G.comp (IsScalarTower.toAlgHom R S₁ C₁) = d.comp Algebra.TensorProduct.includeLeft :=
    ((e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁)))
      (F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y)).2

  have hGa : ∀ a : ↥(Cst S₁ C₁ φ), G (a : C₁) = inrA (gPt e y (a : C₁)) := by
    intro a
    have := AlgHom.congr_fun hstar ((a : C₁) ⊗ₜ[R] (1 : S₁))
    have hφa : φ.toAlgHom ((a : C₁) ⊗ₜ[R] (1 : S₁)) = (1 : S₁) ⊗ₜ[R] (a : C₁) := (mem_Cst S₁ C₁ φ (a : C₁)).mp a.2
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_one, mul_one] at this
    rw [hφa, Algebra.TensorProduct.lift_tmul, map_one, one_mul] at this
    exact this

  have key : F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y =
      F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y ↔ inlA.comp (gPt e y) = G := by
    constructor
    · intro h
      rw [← he₁, h]
    · intro h
      apply (e (P.right : Type u) (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))).injective
      apply Subtype.ext
      rw [he₁, h]
  rw [key]
  constructor
  ·
    intro h a
    have h1 : inlA (gPt e y (a : C₁)) = inrA (gPt e y (a : C₁)) := by
      rw [← hGa a, ← h]; rfl

    let T : Type u := (B ⊗[R] S₁) ⊗[B] (B ⊗[R] S₁)
    let j₁ : B ⊗[R] S₁ →ₐ[R] T := Algebra.TensorProduct.includeLeft
    let j₂ : B ⊗[R] S₁ →ₐ[R] T :=
      (Algebra.TensorProduct.includeRight : (B ⊗[R] S₁) →ₐ[B] (B ⊗[R] S₁) ⊗[B] (B ⊗[R] S₁)).restrictScalars R
    have hcompat : ιU (R := R) S₁ B ≫ algToUnder (A := B ⊗[R] S₁) (B := T) j₁ = ιU (R := R) S₁ B ≫ algToUnder (A := B ⊗[R] S₁) (B := T) j₂ := by
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      change B at b
      show j₁ (b ⊗ₜ[R] (1 : S₁)) = j₂ (b ⊗ₜ[R] (1 : S₁))
      show (b ⊗ₜ[R] (1 : S₁)) ⊗ₜ[B] (1 : B ⊗[R] S₁) = (1 : B ⊗[R] S₁) ⊗ₜ[B] (b ⊗ₜ[R] (1 : S₁))
      have hb : b ⊗ₜ[R] (1 : S₁) = b • (1 : B ⊗[R] S₁) := by
        rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hb, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    let desc : P ⟶ U (R := R) T := pushout.desc (algToUnder (A := B ⊗[R] S₁) (B := T) j₁) (algToUnder (A := B ⊗[R] S₁) (B := T) j₂) hcompat
    have e1 : ∀ z : B ⊗[R] S₁, desc.right.hom (inlA z) = j₁ z := fun z =>
      congrArg (fun (k : U (R := R) (B ⊗[R] S₁) ⟶ U (R := R) T) => k.right.hom z) (pushout.inl_desc _ _ hcompat)
    have e2 : ∀ z : B ⊗[R] S₁, desc.right.hom (inrA z) = j₂ z := fun z =>
      congrArg (fun (k : U (R := R) (B ⊗[R] S₁) ⟶ U (R := R) T) => k.right.hom z) (pushout.inr_desc _ _ hcompat)
    have h2 : (gPt e y (a : C₁)) ⊗ₜ[B] (1 : B ⊗[R] S₁) = (1 : B ⊗[R] S₁) ⊗ₜ[B] (gPt e y (a : C₁)) := by
      have := e1 (gPt e y (a : C₁))
      rw [h1, e2] at this
      exact this.symm
    obtain ⟨b₀, hb₀⟩ := Module.FaithfullyFlat.exists_algebraMap_eq_of_tmul_one_eq_one_tmul h2
    exact ⟨b₀, hb₀⟩
  ·
    intro h
    apply algHom_ext_of_surjective hsurj
    · intro s
      rw [AlgHom.comp_apply, hgS]
      have := AlgHom.congr_fun hGS s
      rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hd₁] at this
      rw [this]; rfl
    · intro a
      obtain ⟨b₀, hb₀⟩ := h a
      rw [AlgHom.comp_apply, hGa, ← hb₀]
      exact hcond b₀

theorem hsheaf_at
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (B : Type u) [CommRing B] [Algebra R B] :
    Function.Injective (F.map (ιU (R := R) S₁ B)) ∧
      ∀ y : F.obj (U (R := R) (B ⊗[R] S₁)),
        F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y = F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) y →
          ∃ x : F.obj (U (R := R) B), F.map (ιU (R := R) S₁ B) x = y := by
  apply hsheaf (U (R := R) B) (U (R := R) (B ⊗[R] S₁)) (ιU (R := R) S₁ B)
  · show (algebraMap B (B ⊗[R] S₁)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · show Function.Surjective (PrimeSpectrum.comap (algebraMap B (B ⊗[R] S₁)))
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

theorem descends_map {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (U (R := R) B)) :
    F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (F.map (ιU (R := R) S₁ B) x) =
      F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (F.map (ιU (R := R) S₁ B) x) := by
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, pushout.condition]

noncomputable def yOf (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B]
    (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) : F.obj (U (R := R) (B ⊗[R] S₁)) :=
  (e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)).symm ⟨gOf hbij f, gOf_comp_toAlgHom hbij f⟩

theorem gPt_yOf (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B]
    (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) : gPt e (yOf e φ hbij f) = gOf hbij f := by
  unfold gPt yOf
  rw [Equiv.apply_symm_apply]

theorem fOf_congr {B : Type u} [CommRing B] [Algebra R B] {g₁ g₂ : C₁ →ₐ[R] B ⊗[R] S₁} (h : g₁ = g₂)
    (h₁ : ∀ a : ↥(Cst S₁ C₁ φ), g₁ (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁))
    (h₂ : ∀ a : ↥(Cst S₁ C₁ φ), g₂ (a : C₁) ∈ Set.range (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] S₁)) :
    fOf g₁ h₁ = fOf g₂ h₂ := by
  subst h; rfl

section Assembly

noncomputable def theta
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (U (R := R) B)) : ↥(Cst S₁ C₁ φ) →ₐ[R] B :=
  fOf (gPt e (F.map (ιU (R := R) S₁ B) x)) ((descends_iff e φ he hφ hbij.2 _).mp (descends_map x))

theorem includeLeft_theta
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (U (R := R) B)) (a : ↥(Cst S₁ C₁ φ)) :
    (theta e φ he hφ hbij x a) ⊗ₜ[R] (1 : S₁) = gPt e (F.map (ιU (R := R) S₁ B) x) (a : C₁) :=
  includeLeft_fOf _ _ a

theorem yOf_descends
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) :
    F.map (pushout.inl (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (yOf e φ hbij f) =
      F.map (pushout.inr (ιU (R := R) S₁ B) (ιU (R := R) S₁ B)) (yOf e φ hbij f) := by
  rw [descends_iff e φ he hφ hbij.2]
  intro a
  rw [gPt_yOf, gOf_coe]
  exact ⟨f a, rfl⟩

noncomputable def psi
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) : F.obj (U (R := R) B) :=
  ((hsheaf_at (S₁ := S₁) hsheaf B).2 (yOf e φ hbij f) (yOf_descends e φ he hφ hbij f)).choose

theorem map_psi
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) :
    F.map (ιU (R := R) S₁ B) (psi e φ hsheaf he hφ hbij f) = yOf e φ hbij f :=
  ((hsheaf_at (S₁ := S₁) hsheaf B).2 (yOf e φ hbij f) (yOf_descends e φ he hφ hbij f)).choose_spec

theorem theta_psi
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) :
    theta e φ he hφ hbij (psi e φ hsheaf he hφ hbij f) = f := by
  have h : gPt e (F.map (ιU (R := R) S₁ B) (psi e φ hsheaf he hφ hbij f)) = gOf hbij f := by
    rw [map_psi, gPt_yOf]
  unfold theta
  rw [fOf_congr φ h _ (fun a => by rw [gOf_coe]; exact ⟨f a, rfl⟩)]
  exact fOf_gOf hbij f _

theorem gPt_map_eq_gOf_theta
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (U (R := R) B)) :
    gPt e (F.map (ιU (R := R) S₁ B) x) = gOf hbij (theta e φ he hφ hbij x) :=
  gOf_unique hbij _ _ (gPt_comp e _) (fun a => (includeLeft_theta e φ he hφ hbij x a).symm)

theorem psi_theta
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B : Type u} [CommRing B] [Algebra R B] (x : F.obj (U (R := R) B)) :
    psi e φ hsheaf he hφ hbij (theta e φ he hφ hbij x) = x := by
  apply (hsheaf_at (S₁ := S₁) hsheaf B).1
  rw [map_psi]

  unfold yOf
  apply (e (B ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁)).symm_apply_eq.mpr
  apply Subtype.ext
  exact (gPt_map_eq_gOf_theta e φ he hφ hbij x).symm

noncomputable def equivB
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) (B : Type u) [CommRing B] [Algebra R B] : (↥(Cst S₁ C₁ φ) →ₐ[R] B) ≃ F.obj (U (R := R) B) where
  toFun := psi e φ hsheaf he hφ hbij
  invFun := theta e φ he hφ hbij
  left_inv := theta_psi e φ hsheaf he hφ hbij
  right_inv := psi_theta e φ hsheaf he hφ hbij

theorem psi_natural
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (ι₀ S₁ C₁ φ)) {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (ψ : B →ₐ[R] B') (f : ↥(Cst S₁ C₁ φ) →ₐ[R] B) :
    psi e φ hsheaf he hφ hbij (ψ.comp f) = F.map (algToUnder ψ) (psi e φ hsheaf he hφ hbij f) := by
  apply (hsheaf_at (S₁ := S₁) hsheaf B').1
  rw [map_psi]

  let ψ' : B ⊗[R] S₁ →ₐ[R] B' ⊗[R] S₁ := Algebra.TensorProduct.map ψ (AlgHom.id R S₁)
  have hsq : algToUnder ψ ≫ ιU (R := R) S₁ B' = ιU (R := R) S₁ B ≫ algToUnder ψ' := by
    rw [ιU, ιU, ← algToUnder_comp, ← algToUnder_comp]
    congr 1
  rw [← FunctorToTypes.map_comp_apply, hsq, FunctorToTypes.map_comp_apply, map_psi]

  apply (e (B' ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B' ⊗[R] S₁)).injective
  apply Subtype.ext
  have hj : ψ'.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B ⊗[R] S₁) =
      (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B' ⊗[R] S₁) := by
    apply AlgHom.ext; intro s
    simp [ψ', Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have h1 : ((e (B' ⊗[R] S₁) (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] B' ⊗[R] S₁))
      (F.map (algToUnder ψ') (yOf e φ hbij f))).1 = ψ'.comp (gOf hbij f) := by
    rw [← e_congr F S₁ C₁ e hj]
    have := he (B ⊗[R] S₁) (B' ⊗[R] S₁) Algebra.TensorProduct.includeRight ψ' (yOf e φ hbij f)
    refine this.trans ?_
    congr 1
    exact gPt_yOf e φ hbij f
  rw [h1]
  show gPt e (yOf e φ hbij (ψ.comp f)) = ψ'.comp (gOf hbij f)
  rw [gPt_yOf]
  symm
  apply gOf_unique hbij
  · rw [AlgHom.comp_assoc, gOf_comp_toAlgHom, hj]
  · intro a
    rw [AlgHom.comp_apply, gOf_coe]
    simp [ψ', Algebra.TensorProduct.map_tmul]

end Assembly

end Main

end AffD
p2m_reactivate "P2MW.S_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ.AffD"

open AffD in
theorem solution
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (hsheaf : ∀ (B B' : Under (CommRingCat.of R)) (φ : B ⟶ B'),
      φ.right.hom.Flat → Function.Surjective (PrimeSpectrum.comap φ.right.hom) →
        Function.Injective (F.map φ) ∧
        ∀ y : F.obj B', F.map (pushout.inl φ φ) y = F.map (pushout.inr φ φ) y → ∃ x : F.obj B, F.map φ x = y)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁] [Module.FaithfullyFlat R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1)
    (φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁)
    (hφ : ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom)
    (hbij : Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S₁ C₁)
      (AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : C₁ →ₐ[R] C₁ ⊗[R] S₁))
        (Algebra.TensorProduct.includeRight : C₁ →ₐ[R] S₁ ⊗[R] C₁)).val (fun s a => Commute.all _ _))) :
    ∃ C : Under (CommRingCat.of R), Nonempty (F.CorepresentableBy C) := by
  classical
  have hbij' : Function.Bijective (ι₀ S₁ C₁ φ) := hbij
  refine ⟨U (R := R) ↥(Cst S₁ C₁ φ), ⟨?_⟩⟩
  exact
    { homEquiv := fun {Y} =>
        letI : Algebra R (Y.right : Type u) := (show R →+* Y.right from Y.hom.hom).toAlgebra
        (homEquivAlg (R := R) (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u))).trans
          (equivB e φ hsheaf he hφ hbij' (Y.right : Type u))
      homEquiv_comp := by
        intro Y Y' g k
        letI iY : Algebra R (Y.right : Type u) := (show R →+* Y.right from Y.hom.hom).toAlgebra
        letI iY' : Algebra R (Y'.right : Type u) := (show R →+* Y'.right from Y'.hom.hom).toAlgebra
        show psi e φ hsheaf he hφ hbij' (underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y'.right : Type u)) (k ≫ g)) =
          F.map g (psi e φ hsheaf he hφ hbij' (underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u)) k))
        have hg : algToUnder (underToAlg (A := (Y.right : Type u)) (B := (Y'.right : Type u)) g) = g :=
          algToUnder_underToAlg _
        have h1 : underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y'.right : Type u)) (k ≫ g) =
            (underToAlg (A := (Y.right : Type u)) (B := (Y'.right : Type u)) g).comp
              (underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u)) k) :=
          underToAlg_comp (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u)) (D := (Y'.right : Type u)) k g
        rw [h1, psi_natural e φ hsheaf he hφ hbij']
        exact congrArg (fun (m : Y ⟶ Y') => F.map m (psi e φ hsheaf he hφ hbij' (underToAlg (A := ↥(Cst S₁ C₁ φ)) (B := (Y.right : Type u)) k))) hg }

end S_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ
end P2MW
export P2MW.S_CategoryTheory_Functor_exists_corepresentableBy_of_descentDatum_of_bijective_univ (solution)
