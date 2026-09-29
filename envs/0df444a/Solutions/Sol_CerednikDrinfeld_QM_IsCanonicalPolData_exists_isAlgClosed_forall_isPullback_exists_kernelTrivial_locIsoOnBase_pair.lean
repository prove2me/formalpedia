-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsCanonicalPolData.exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/c11ecda8-184f-5282-8823-0df6d9569351

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_pullback_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_Polarisation_LocIsoOnBase_equivalence
import Theorems.Thm_AlgebraicGeometry_Polarisation_KernelTrivial_pullback_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_forall_mul_comp_eq_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair

set_option autoImplicit false

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

namespace RootPair

variable {R : Type u} [CommRing R]

theorem mul_val_congr {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (ht : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f)
    (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) : (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst ht; cases Subtype.ext hP; cases Subtype.ext hQ; rfl

theorem schemeHomOverComp_inv {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI : Group (SchemeHomOver t f) := L.pointGroup t
  letI : Group (SchemeHomOver t' f) := L.pointGroup t'
  let Φ : SchemeHomOver t f →* SchemeHomOver t' f :=
    MonoidHom.mk' (fun x => schemeHomOverComp ψ hψ x) (fun x y => L.mul_natural t t' ψ hψ x y)
  exact map_inv Φ x

theorem locIso_of_iso {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R)) {M M' : X.Modules} (i : M ≅ M') :
    LocIsoOnBase g M M' :=
  fun _ => ⟨⊤, trivial, ⟨(Scheme.Modules.pullback (g ⁻¹ᵁ ⊤).ι).mapIso i⟩⟩

theorem negMor_comp_of_hom {S' S'' : Type u} [CommRing S'] [CommRing S'']
    {A' A'' : Scheme.{u}} {f' : A' ⟶ Spec (CommRingCat.of S')} {f'' : A'' ⟶ Spec (CommRingCat.of S'')}
    (L' : RelativeGroupLaw S' f') (L'' : RelativeGroupLaw S'' f'')
    (h : A'' ⟶ A') (τ : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S')) (hh : h ≫ f' = f'' ≫ τ)
    (hmul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S'')) (P Q : SchemeHomOver t f''),
      (L''.mul t P Q).1 ≫ h =
        (L'.mul (t ≫ τ) ⟨P.1 ≫ h, by rw [Category.assoc, hh, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ h, by rw [Category.assoc, hh, ← Category.assoc, Q.2]⟩).1) :
    negMor f'' L'' ≫ h = h ≫ negMor f' L' := by
  letI G1 : Group (SchemeHomOver f'' f'') := L''.pointGroup f''
  letI G2 : Group (SchemeHomOver (f'' ≫ τ) f') := L'.pointGroup (f'' ≫ τ)
  let Φ : SchemeHomOver f'' f'' →* SchemeHomOver (f'' ≫ τ) f' :=
    MonoidHom.mk'
      (fun x => (⟨x.1 ≫ h, by rw [Category.assoc, hh, ← Category.assoc, x.2]⟩ : SchemeHomOver (f'' ≫ τ) f'))
      (fun x y => Subtype.ext (hmul f'' x y))
  have h1 : (L''.inv f'' (idPt f'')).1 ≫ h = (L'.inv (f'' ≫ τ) (Φ (idPt f''))).1 :=
    congrArg Subtype.val (map_inv Φ (idPt f''))
  have h2 := congrArg Subtype.val (schemeHomOverComp_inv L' f' (f'' ≫ τ) h hh (idPt f'))
  have h3 : schemeHomOverComp h hh (idPt f') = Φ (idPt f'') :=
    Subtype.ext (show h ≫ 𝟙 A' = 𝟙 A'' ≫ h by rw [Category.comp_id, Category.id_comp])
  rw [h3, schemeHomOverComp_coe] at h2
  calc negMor f'' L'' ≫ h = (L''.inv f'' (idPt f'')).1 ≫ h := rfl
    _ = (L'.inv (f'' ≫ τ) (Φ (idPt f''))).1 := h1
    _ = h ≫ (L'.inv f' (idPt f')).1 := h2.symm
    _ = h ≫ negMor f' L' := rfl

theorem transfer {k : Type u} [CommRing k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    (𝓛 : A.Modules)
    (S' : Type u) [CommRing S'] [Algebra k S']
    (H : ∀ (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S'))
            (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap k S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))),
                  by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧
          KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback
              (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L')).obj 𝓛₀))
    (k'' : Type u) [CommRing k''] [Algebra k k''] (φ : S' →+* k'')
    (hφ : φ.comp (algebraMap k S') = algebraMap k k'')
    {A'' : Scheme.{u}} (f'' : A'' ⟶ Spec (CommRingCat.of k'')) (g : A'' ⟶ A)
    (hg : IsPullback g f'' f (Spec.map (CommRingCat.ofHom (algebraMap k k''))))
    (L'' : RelativeGroupLaw k'' f'')
    (hL'' : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k'')) (P Q : SchemeHomOver t' f''),
        (L''.mul t' P Q).1 ≫ g =
          (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'')))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) :
    ∃ 𝓛₁ : A''.Modules, Scheme.Modules.IsInvertible 𝓛₁ ∧ KernelTrivial f'' L'' 𝓛₁ ∧
      LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓛) (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓛₁) := by

  obtain ⟨L', hL'mul, -, -⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_forall_mul_comp_eq_of_isPullback
    f (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L
  obtain ⟨𝓛₀, h0inv, h0K, h0loc⟩ := H L' (fun T t' P Q => hL'mul t' P Q)

  have hστ : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap k S')) =
      Spec.map (CommRingCat.ofHom (algebraMap k k'')) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  let h : A'' ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap k S'))) :=
    pullback.lift g (f'' ≫ Spec.map (CommRingCat.ofHom φ)) (by rw [hg.w, Category.assoc, hστ])
  have hh1 : h ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))) = g := pullback.lift_fst _ _ _
  have hh2 : h ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))) =
      f'' ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  have hpb : IsPullback h f'' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))
      (Spec.map (CommRingCat.ofHom φ)) := by
    have big : IsPullback (h ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) f'' f
        (Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap k S'))) := by
      rw [hh1, hστ]; exact hg
    exact IsPullback.of_right big hh2 (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))

  have hmul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of k''))
      (P Q : SchemeHomOver t' f''),
      (L''.mul t' P Q).1 ≫ h =
        (L'.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨P.1 ≫ h, by rw [Category.assoc, hpb.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ h, by rw [Category.assoc, hpb.w, ← Category.assoc, Q.2]⟩).1 := by
    intro T t' P Q
    apply pullback.hom_ext
    · rw [Category.assoc, hh1, hL'' t' P Q, hL'mul]
      apply mul_val_congr L
      · rw [Category.assoc, hστ]
      · show P.1 ≫ g = (P.1 ≫ h) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S')))
        rw [Category.assoc, hh1]
      · show Q.1 ≫ g = (Q.1 ≫ h) ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S')))
        rw [Category.assoc, hh1]
    · have e1 : ((L''.mul t' P Q).1 ≫ h) ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S'))) =
          t' ≫ Spec.map (CommRingCat.ofHom φ) := by
        rw [Category.assoc, hh2, ← Category.assoc, (L''.mul t' P Q).2]
      exact e1.trans ((L'.mul _ _ _).2).symm
  refine ⟨(Scheme.Modules.pullback h).obj 𝓛₀, Scheme.Modules.IsInvertible.pullback h h0inv, ?_, ?_⟩
  · exact AlgebraicGeometry.Polarisation.KernelTrivial.pullback_of_isPullback φ hpb L' L''
      (fun t' P Q => hmul t' P Q) 𝓛₀ h0inv h0K
  · have Eq := LocIsoOnBase.equivalence f''
    have h1 := LocIsoOnBase.pullback_of_comp_eq f'' h (Spec.map (CommRingCat.ofHom φ)) hh2 h0loc
    have hneg : negMor f'' L'' ≫ h =
        h ≫ negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L' :=
      negMor_comp_of_hom L' L'' h (Spec.map (CommRingCat.ofHom φ)) hh2 (fun t P Q => hmul t P Q)
    let iso1 : (Scheme.Modules.pullback h).obj
          ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))).obj 𝓛) ≅
        (Scheme.Modules.pullback g).obj 𝓛 :=
      (Scheme.Modules.pullbackComp h (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k S'))))).app 𝓛 ≪≫
        (Scheme.Modules.pullbackCongr hh1).app 𝓛
    let iso2 : (Scheme.Modules.pullback h).obj
          (𝓛₀ ⊗ (Scheme.Modules.pullback
            (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L')).obj 𝓛₀) ≅
        (Scheme.Modules.pullback h).obj 𝓛₀ ⊗
          (Scheme.Modules.pullback (negMor f'' L'')).obj ((Scheme.Modules.pullback h).obj 𝓛₀) :=
      Scheme.Modules.pullbackTensorObjIso h _ _ ≪≫
        (Iso.refl _ ⊗ᵢ
          ((Scheme.Modules.pullbackComp h
              (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k S')))) L')).app 𝓛₀ ≪≫
            (Scheme.Modules.pullbackCongr hneg.symm).app 𝓛₀ ≪≫
            ((Scheme.Modules.pullbackComp (negMor f'' L'') h).app 𝓛₀).symm))
    exact Eq.trans (Eq.trans (Eq.symm (locIso_of_iso _ iso1)) h1) (locIso_of_iso _ iso2)

end RootPair

theorem solution
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I)
    (𝓛 𝓜 : A.Modules) (h𝓛 : IsCanonicalPolData f L act act_over star 𝓛) (h𝓜 : IsCanonicalPolData f L act act_over star 𝓜) :
    ∃ (k'' : Type) (_ : Field k'') (_ : IsAlgClosed k'') (_ : Algebra k k''),
      ∀ {A'' : Scheme} (f'' : A'' ⟶ Spec (CommRingCat.of k'')) (g : A'' ⟶ A)
        (hg : IsPullback g f'' f (Spec.map (CommRingCat.ofHom (algebraMap k k''))))
        (L'' : RelativeGroupLaw k'' f''),
        (∀ {T : Scheme} (t' : T ⟶ Spec (CommRingCat.of k'')) (P Q : SchemeHomOver t' f''),
            (L''.mul t' P Q).1 ≫ g =
              (L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap k k'')))
                ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) →
        (∃ 𝓛₁ : A''.Modules, Scheme.Modules.IsInvertible 𝓛₁ ∧ KernelTrivial f'' L'' 𝓛₁ ∧
            LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓛) (𝓛₁ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓛₁)) ∧
        (∃ 𝓜₁ : A''.Modules, Scheme.Modules.IsInvertible 𝓜₁ ∧ KernelTrivial f'' L'' 𝓜₁ ∧
            LocIsoOnBase f'' ((Scheme.Modules.pullback g).obj 𝓜) (𝓜₁ ⊗ (Scheme.Modules.pullback (negMor f'' L'')).obj 𝓜₁)) := by
  classical
  obtain ⟨-, -, -, ⟨S₁, i₁, j₁, hff₁, H₁⟩, -, -⟩ := h𝓛
  obtain ⟨-, -, -, ⟨S₂, i₂, j₂, hff₂, H₂⟩, -, -⟩ := h𝓜
  letI := i₁; letI := j₁; letI := i₂; letI := j₂
  haveI := hff₁; haveI := hff₂

  haveI : Nontrivial S₂ := (TensorProduct.lid k S₂).symm.toEquiv.nontrivial
  haveI : Nontrivial (S₁ ⊗[k] S₂) := inferInstance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (S₁ ⊗[k] S₂)
  haveI := h𝔪
  letI instK : Field ((S₁ ⊗[k] S₂) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let ψ : S₁ ⊗[k] S₂ →+* AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪) :=
    (algebraMap ((S₁ ⊗[k] S₂) ⧸ 𝔪) (AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪))).comp (Ideal.Quotient.mk 𝔪)
  let φ₁ : S₁ →+* AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪) := ψ.comp Algebra.TensorProduct.includeLeftRingHom
  let φ₂ : S₂ →+* AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪) :=
    ψ.comp (Algebra.TensorProduct.includeRight (R := k) (A := S₁) (B := S₂)).toRingHom
  letI alg : Algebra k (AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪)) := (φ₁.comp (algebraMap k S₁)).toAlgebra
  have hφ₁ : φ₁.comp (algebraMap k S₁) = algebraMap k (AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪)) := rfl
  have hφ₂ : φ₂.comp (algebraMap k S₂) = algebraMap k (AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪)) := by
    rw [← hφ₁]
    ext r
    change ψ ((Algebra.TensorProduct.includeRight (R := k) (A := S₁) (B := S₂)) (algebraMap k S₂ r)) =
      ψ ((algebraMap k S₁ r) ⊗ₜ (1 : S₂))
    rw [Algebra.TensorProduct.includeRight_apply, ← Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply]
  refine ⟨AlgebraicClosure ((S₁ ⊗[k] S₂) ⧸ 𝔪), inferInstance, inferInstance, alg, ?_⟩
  intro A'' f'' g hg L'' hL''
  exact ⟨RootPair.transfer f L 𝓛 S₁ H₁ _ φ₁ hφ₁ f'' g hg L'' (fun t' P Q => hL'' t' P Q),
    RootPair.transfer f L 𝓜 S₂ H₂ _ φ₂ hφ₂ f'' g hg L'' (fun t' P Q => hL'' t' P Q)⟩

end S_CerednikDrinfeld_QM_IsCanonicalPolData_exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsCanonicalPolData_exists_isAlgClosed_forall_isPullback_exists_kernelTrivial_locIsoOnBase_pair (solution)
