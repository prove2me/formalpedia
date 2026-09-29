-- Prove2me | solution 1 for CerednikDrinfeld.QM.ModuliTowerWitnessD.germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9f45ae13-d238-57cc-a18d-5a5bc0eb594e

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMModuliTowerD
import Mathlib
import Theorems.Thm_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitnessD_germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

open CategoryTheory.Limits
open scoped Pointwise

noncomputable section

namespace MFFGen

universe u v

namespace FunctionFieldPull

variable {X Y Z : Scheme.{u}}

def pull [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y) : Y.functionField ⟶ X.functionField :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap (genericPoint X)

section

variable [IrreducibleSpace X] [IrreducibleSpace Y] [IrreducibleSpace Z]

theorem pull_germ (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) (hU : genericPoint Y ∈ U) (s : Γ(Y, U)) :
    pull f h (Y.presheaf.germ U (genericPoint Y) hU s) =
      X.presheaf.germ (f ⁻¹ᵁ U) (genericPoint X) (h.mem_open U.isOpen hU) (f.app U s) := by
  simp only [pull, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, Scheme.Hom.germ_stalkMap_apply]

theorem pull_algebraMap (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y) (x : X)
    (a : Y.presheaf.stalk (f.base x)) :
    pull f h (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  simp only [pull, RingHom.algebraMap_toAlgebra, CommRingCat.comp_apply]
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply (Y.presheaf)]
  have := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint X) x
    ((genericPoint_spec X).specializes trivial) a
  convert this using 2

theorem pull_id : pull (𝟙 X) (specializes_refl _) = 𝟙 _ := by
  simp [pull]

theorem pull_comp (f : X ⟶ Y) (g : Y ⟶ Z) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint Y) ⤳ genericPoint Z) :
    pull (f ≫ g) ((g.base.hom.map_specializes hf).trans hg) = pull g hg ≫ pull f hf := by
  simp only [pull, Scheme.Hom.stalkMap_comp, Category.assoc]
  rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g (f.base (genericPoint X)) (genericPoint Y) hf]
  rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
  rfl

end

variable [IsIntegral X] [IsIntegral Y]

theorem specializes_of_iso (e : X ≅ Y) : e.hom.base (genericPoint X) ⤳ genericPoint Y :=
  (genericPoint_eq_of_isOpenImmersion e.hom).symm ▸ specializes_refl _

theorem specializes_of_iso_inv (e : X ≅ Y) : e.inv.base (genericPoint Y) ⤳ genericPoint X :=
  specializes_of_iso e.symm

def equivOfIso (e : X ≅ Y) : Y.functionField ≃+* X.functionField :=
  (({ hom := pull e.hom (specializes_of_iso e)
      inv := pull e.inv (specializes_of_iso_inv e)
      hom_inv_id := by
        have h := (pull_comp e.inv e.hom (specializes_of_iso_inv e) (specializes_of_iso e)).symm
        rw [h]
        have : ∀ (k : (e.inv ≫ e.hom).base (genericPoint Y) ⤳ genericPoint Y),
            pull (e.inv ≫ e.hom) k = 𝟙 _ := by
          rw [e.inv_hom_id]; intro k; exact pull_id
        exact this _
      inv_hom_id := by
        have h := (pull_comp e.hom e.inv (specializes_of_iso e) (specializes_of_iso_inv e)).symm
        rw [h]
        have : ∀ (k : (e.hom ≫ e.inv).base (genericPoint X) ⤳ genericPoint X),
            pull (e.hom ≫ e.inv) k = 𝟙 _ := by
          rw [e.hom_inv_id]; intro k; exact pull_id
        exact this _ } : Y.functionField ≅ X.functionField)).commRingCatIsoToRingEquiv

theorem equivOfIso_apply (e : X ≅ Y) (a : Y.functionField) :
    equivOfIso e a = pull e.hom (specializes_of_iso e) a := rfl

theorem equivOfIso_symm_apply (e : X ≅ Y) (a : X.functionField) :
    (equivOfIso e).symm a = pull e.inv (specializes_of_iso_inv e) a := rfl

theorem map_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range.map
        (equivOfIso e).toRingHom =
      (algebraMap (X.presheaf.stalk x) X.functionField).range := by
  haveI : IsIso (e.hom.stalkMap x) := inferInstance
  ext b
  simp only [Subring.mem_map, RingHom.mem_range, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨e.hom.stalkMap x a, (pull_algebraMap e.hom (specializes_of_iso e) x a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ : ∃ a', e.hom.stalkMap x a' = a :=
      ⟨inv (e.hom.stalkMap x) a, by
        rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]; rfl⟩
    exact ⟨_, ⟨a', rfl⟩, pull_algebraMap e.hom (specializes_of_iso e) x a'⟩

theorem image_equivOfIso_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e) ''
        ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) =
      ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) := by
  have h := congrArg (fun S : Subring X.functionField => (S : Set X.functionField))
    (map_equivOfIso_range_stalk e x)
  simpa [Subring.coe_map] using h

theorem image_equivOfIso_symm_range_stalk (e : X ≅ Y) (x : X) :
    (equivOfIso e).symm '' ((algebraMap (X.presheaf.stalk x) X.functionField).range : Set _) =
      ((algebraMap (Y.presheaf.stalk (e.hom.base x)) Y.functionField).range : Set _) := by
  rw [← image_equivOfIso_range_stalk e x, ← Set.image_comp]
  simp

theorem pull_baseToFunctionField {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (hf : f ≫ cY = cX)
    (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX a := by
  subst hf
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) =
    X.presheaf.germ ⊤ (genericPoint X) trivial _
  rw [pull_germ]
  rfl

theorem equivOfIso_baseToFunctionField {K : Type u} [Field K] (e : X ≅ Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K))
    (hf : e.hom ≫ cY = cX) (a : K) :
    equivOfIso e (baseToFunctionField cY a) = baseToFunctionField cX a :=
  pull_baseToFunctionField e.hom _ cX cY hf a

end FunctionFieldPull

open FunctionFieldPull

section PullExtras
variable {X Y : Scheme.{u}} [IrreducibleSpace ↥X] [IrreducibleSpace ↥Y]

theorem pull_baseToFunctionField_twist [IsIntegral X] [IsIntegral Y] {K : Type u} [Field K] (f : X ⟶ Y)
    (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K)) (cY : Y ⟶ Spec (CommRingCat.of K)) (τ : K ≃+* K)
    (hf : f ≫ cY = cX ≫ Spec.map (CommRingCat.ofHom (τ : K →+* K))) (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX (τ a) := by
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) = X.presheaf.germ ⊤ (genericPoint X) trivial _
  rw [pull_germ]
  have key : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
      cX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (τ a)) := by
    have h1 : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
        cX.appTop.hom ((Spec.map (CommRingCat.ofHom (τ : K →+* K))).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
      congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) hf
    rw [h1]
    congr 1
    have h2 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (τ : K →+* K)))
    exact h2.symm
  exact congrArg _ key

theorem pull_germToFunctionField [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (U : Y.Opens) [hU : Nonempty (Scheme.Opens.toScheme U)] [hU' : Nonempty (Scheme.Opens.toScheme (f ⁻¹ᵁ U))] (t : Γ(Y, U)) :
    pull f h (Y.germToFunctionField U t) = X.germToFunctionField (f ⁻¹ᵁ U) ((f.app U).hom t) := by
  obtain ⟨⟨y, hy⟩⟩ := hU
  exact pull_germ f h U (((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨y, trivial, hy⟩) t

theorem pull_congr' (f g : X ⟶ Y) (hfg : f = g) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint X) ⤳ genericPoint Y) : pull f hf = pull g hg := by
  subst hfg; rfl

theorem pull_baseToFunctionField_map [IsIntegral X] [IsIntegral Y] {K K' : Type u} [Field K] [Field K']
    (f : X ⟶ Y) (h : f.base (genericPoint X) ⤳ genericPoint Y)
    (cX : X ⟶ Spec (CommRingCat.of K')) (cY : Y ⟶ Spec (CommRingCat.of K)) (τ : K →+* K')
    (hf : f ≫ cY = cX ≫ Spec.map (CommRingCat.ofHom τ)) (a : K) :
    pull f h (baseToFunctionField cY a) = baseToFunctionField cX (τ a) := by
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change pull f h (Y.presheaf.germ ⊤ (genericPoint Y) trivial _) = X.presheaf.germ ⊤ (genericPoint X) trivial _
  rw [pull_germ]
  have key : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
      cX.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K')).inv.hom (τ a)) := by
    have h1 : (f.app ⊤).hom (cY.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) =
        cX.appTop.hom ((Spec.map (CommRingCat.ofHom τ)).appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) :=
      congrArg (fun φ => (Scheme.Hom.appTop φ).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) hf
    rw [h1]
    congr 1
    have h2 := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ))
    exact h2.symm
  exact congrArg _ key

theorem pull_comp_apply [IrreducibleSpace ↥X] {Z : Scheme.{u}} [IrreducibleSpace ↥Z] (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : f.base (genericPoint X) ⤳ genericPoint Y) (hg : g.base (genericPoint Y) ⤳ genericPoint Z)
    (hfg : (f ≫ g).base (genericPoint X) ⤳ genericPoint Z) (y : Z.functionField) :
    pull (f ≫ g) hfg y = pull f hf (pull g hg y) := by
  rw [show pull (f ≫ g) hfg = pull g hg ≫ pull f hf from pull_comp f g hf hg]; rfl

theorem pull_congr_apply (f g : X ⟶ Y) (hfg : f = g) (hf : f.base (genericPoint X) ⤳ genericPoint Y)
    (hg : g.base (genericPoint X) ⤳ genericPoint Y) (y : Y.functionField) : pull f hf y = pull g hg y := by
  subst hfg; rfl

end PullExtras

theorem closure_transfer {P Q C A B : Type*} [Field P] [Field Q] (E : P ≃+* Q)
    (bP : C → P) (bQ : C → Q) (hb : ∀ c, bQ c = E (bP c)) (pr : B → P) (β : A → B)
    (hβ : Function.Surjective β) (j : A → Q) (hj : ∀ a, j a = E (pr (β a)))
    (H : Subfield.closure (Set.range bP ∪ Set.range pr) = ⊤) :
    Subfield.closure (Set.range bQ ∪ Set.range j) = ⊤ := by
  have hS : Set.range bQ ∪ Set.range j = (E : P →+* Q) '' (Set.range bP ∪ Set.range pr) := by
    ext y
    simp only [Set.mem_union, Set.mem_range, Set.mem_image, RingHom.coe_coe]
    constructor
    · rintro (⟨c, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨bP c, Or.inl ⟨c, rfl⟩, (hb c).symm⟩
      · exact ⟨pr (β a), Or.inr ⟨β a, rfl⟩, (hj a).symm⟩
    · rintro ⟨x, (⟨c, rfl⟩ | ⟨b, rfl⟩), rfl⟩
      · exact Or.inl ⟨c, hb c⟩
      · obtain ⟨a, rfl⟩ := hβ b
        exact Or.inr ⟨a, hj a⟩
  rw [hS, ← RingHom.map_field_closure, H]
  exact eq_top_iff.2 fun y _ => Subfield.mem_map.2 ⟨E.symm y, Subfield.mem_top _, E.apply_symm_apply y⟩

theorem linIndep_transfer {k A B P Q C : Type*} [Field k] [Field A] [Algebra k A] [Field B]
    [Field P] [Field Q] [Field C] (β : A ≃+* B) (bk : k → B) (hβk : ∀ a, β (algebraMap k A a) = bk a)
    (E : P ≃+* Q) (bP : C → P) (bQ : C → Q) (hb : ∀ c, bQ c = E (bP c)) (pr : B → P) (j : A → Q)
    (hj : ∀ a, j a = E (pr (β a)))
    (H : ∀ t : Finset B, (∀ d : t → k, (∑ y : t, bk (d y) * (y : B)) = 0 → ∀ y : t, d y = 0) →
      ∀ c : t → C, (∑ y : t, bP (c y) * pr (y : B)) = 0 → ∀ y : t, c y = 0)
    (t : Finset A) (ht : LinearIndependent k (fun x : t => (x : A))) (c : t → C)
    (hc : (∑ x : t, bQ (c x) * j (x : A)) = 0) (x : t) : c x = 0 := by
  classical
  let t' : Finset B := t.map β.toEquiv.toEmbedding
  have hmem : ∀ x : t, β (x : A) ∈ t' := fun x => Finset.mem_map_of_mem _ x.2
  have hmem' : ∀ y : t', β.symm (y : B) ∈ t := fun y => by
    obtain ⟨a, ha, hay⟩ := Finset.mem_map.1 y.2
    have : β.symm (y : B) = a := by rw [← hay]; exact β.symm_apply_apply a
    rw [this]; exact ha
  let e : t ≃ t' :=
    { toFun := fun x => ⟨β (x : A), hmem x⟩
      invFun := fun y => ⟨β.symm (y : B), hmem' y⟩
      left_inv := fun x => Subtype.ext (β.symm_apply_apply _)
      right_inv := fun y => Subtype.ext (β.apply_symm_apply _) }
  have key := H t' ?_ (c ∘ e.symm) ?_ (e x)
  · have : (c ∘ ⇑e.symm) (e x) = c x := by simp
    rw [← this]; exact key
  · intro d hd y
    have ht' := (Fintype.linearIndependent_iff.1 ht) (d ∘ e)
    have hsum : (∑ x : t, (d ∘ e) x • ((x : t) : A)) = 0 := by
      apply β.injective
      rw [map_sum, map_zero]
      simp only [Function.comp_apply, Algebra.smul_def, map_mul, hβk]
      rw [← hd]
      exact Fintype.sum_equiv e _ _ (fun x => rfl)
    have := ht' hsum (e.symm y)
    simpa using this
  · apply E.injective
    rw [map_sum, map_zero, ← hc]
    simp only [Function.comp_apply, map_mul, ← hb]
    exact Fintype.sum_equiv e.symm _ _ (fun y => by simp [e, hj])

theorem injective_of_localizationAway {n : ℤ} {K : Type} [Field K] [CharZero K]
    (φ : Localization.Away n →+* K) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers n) x
  have hcast : ∀ b : ℤ, φ (algebraMap ℤ (Localization.Away n) b) = (b : K) := fun b =>
    eq_intCast (φ.comp (algebraMap ℤ (Localization.Away n))) b
  have ha : (a : K) = 0 := by
    have h1 := congrArg φ (IsLocalization.mk'_spec (Localization.Away n) a s)
    rw [map_mul, hcast a] at h1
    rw [show φ (IsLocalization.mk' (Localization.Away n) a s) = 0 from hx, zero_mul] at h1
    exact h1.symm
  have ha0 : a = 0 := by exact_mod_cast ha
  show IsLocalization.mk' (Localization.Away n) a s = 0
  rw [ha0, IsLocalization.mk'_zero]

theorem ringHom_ext_localizationAway {n : ℤ} {K : Type} [CommRing K] (φ ψ : Localization.Away n →+* K) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers n) (RingHom.ext_int _ _)

end MFFGen

end

set_option maxHeartbeats 3200000 in

theorem solution
    {N q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (D : ℕ)
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)
    (gal : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (tw : ModuliTowerWitnessD Λ N q q' D Fbar X πX sbar pt 𝔐 e𝔐 gal 𝕋 galT W WT)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))

    (g : 𝔐.C ⟶ 𝔐.C)
    (hg₁ : g ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar = e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar)
    (hg₂ : g ≫ 𝔐.toBase = 𝔐.toBase ≫ Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))
    (x : Fbar) (U : 𝔐.C.Opens) (hU : (genericPoint (𝔐.C : Scheme.{0})) ∈ U)
    (hU' : (genericPoint (𝔐.C : Scheme.{0})) ∈ g ⁻¹ᵁ U) (sec : 𝔐.C.presheaf.obj (Opposite.op U))
    (hsec : (𝔐.C.presheaf.germ U (genericPoint (𝔐.C : Scheme.{0})) hU).hom sec = 𝔐.ffEquiv x) :
    (𝔐.C.presheaf.germ (g ⁻¹ᵁ U) (genericPoint (𝔐.C : Scheme.{0})) hU').hom ((g.app U).hom sec) = 𝔐.ffEquiv (gal σ • x) := by
  classical

  have hsb : ∀ ρ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ, Spec.map (CommRingCat.ofHom ρ) ≫ sbar = sbar := by
    intro ρ
    rw [← Spec.map_preimage sbar, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (MFFGen.ringHom_ext_localizationAway _ _)
  let σr : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ := (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
  let σr' : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ := (σ.symm : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)
  have hσσ' : σr.comp σr' = RingHom.id _ := RingHom.ext fun z => σ.apply_symm_apply z
  have hσ'σ : σr'.comp σr = RingHom.id _ := RingHom.ext fun z => σ.symm_apply_apply z
  let tσ : Limits.pullback πX sbar ⟶ Limits.pullback πX sbar :=
    Limits.pullback.lift (Limits.pullback.fst πX sbar) (Limits.pullback.snd πX sbar ≫ Spec.map (CommRingCat.ofHom σr))
      (by rw [Category.assoc, hsb]; exact Limits.pullback.condition)
  let tσ' : Limits.pullback πX sbar ⟶ Limits.pullback πX sbar :=
    Limits.pullback.lift (Limits.pullback.fst πX sbar) (Limits.pullback.snd πX sbar ≫ Spec.map (CommRingCat.ofHom σr'))
      (by rw [Category.assoc, hsb]; exact Limits.pullback.condition)
  have tσ_fst : tσ ≫ Limits.pullback.fst πX sbar = Limits.pullback.fst πX sbar := Limits.pullback.lift_fst _ _ _
  have tσ_snd : tσ ≫ Limits.pullback.snd πX sbar = Limits.pullback.snd πX sbar ≫ Spec.map (CommRingCat.ofHom σr) :=
    Limits.pullback.lift_snd _ _ _
  have tσ'_fst : tσ' ≫ Limits.pullback.fst πX sbar = Limits.pullback.fst πX sbar := Limits.pullback.lift_fst _ _ _
  have tσ'_snd : tσ' ≫ Limits.pullback.snd πX sbar = Limits.pullback.snd πX sbar ≫ Spec.map (CommRingCat.ofHom σr') :=
    Limits.pullback.lift_snd _ _ _
  have hSpec1 : Spec.map (CommRingCat.ofHom σr) ≫ Spec.map (CommRingCat.ofHom σr') = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
    exact CommRingCat.hom_ext (by simpa [CommRingCat.hom_comp] using hσσ')
  have hSpec2 : Spec.map (CommRingCat.ofHom σr') ≫ Spec.map (CommRingCat.ofHom σr) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; congr 1
    exact CommRingCat.hom_ext (by simpa [CommRingCat.hom_comp] using hσ'σ)
  have ht1 : tσ ≫ tσ' = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, tσ'_fst, tσ_fst, Category.id_comp]
    · rw [Category.assoc, tσ'_snd, ← Category.assoc, tσ_snd, Category.assoc, hSpec1, Category.comp_id, Category.id_comp]
  have ht2 : tσ' ≫ tσ = 𝟙 _ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, tσ_fst, tσ'_fst, Category.id_comp]
    · rw [Category.assoc, tσ_snd, ← Category.assoc, tσ'_snd, Category.assoc, hSpec2, Category.comp_id, Category.id_comp]
  haveI : IsIso tσ := ⟨⟨tσ', ht1, ht2⟩⟩
  have hge : g ≫ e𝔐 = e𝔐 ≫ tσ := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hg₁, Category.assoc, tσ_fst]
    · rw [Category.assoc, he𝔐, hg₂, Category.assoc, tσ_snd, ← Category.assoc, he𝔐]
  have hgeq : g = e𝔐 ≫ tσ ≫ CategoryTheory.inv e𝔐 := by
    rw [← Category.assoc, ← hge, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  haveI hgiso : IsIso g := by rw [hgeq]; infer_instance
  have hgs : g.base (genericPoint 𝔐.C) ⤳ genericPoint 𝔐.C := MFFGen.FunctionFieldPull.specializes_of_iso (asIso g)

  let Eg : 𝔐.C.functionField ≃+* 𝔐.C.functionField := MFFGen.FunctionFieldPull.equivOfIso (asIso g)
  have hEg : ∀ y, Eg y = MFFGen.FunctionFieldPull.pull g hgs y := fun y => rfl
  let Wr : Fbar ≃+* Fbar := 𝔐.ffEquiv.trans (Eg.trans 𝔐.ffEquiv.symm)
  have hWr : ∀ z, Wr z = 𝔐.ffEquiv.symm (MFFGen.FunctionFieldPull.pull g hgs (𝔐.ffEquiv z)) := fun z => rfl
  have hWconst : ∀ c : AlgebraicClosure ℚ, Wr (algebraMap (AlgebraicClosure ℚ) Fbar c) =
      algebraMap (AlgebraicClosure ℚ) Fbar ((σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) c) := by
    intro c
    rw [hWr, 𝔐.ffEquiv_algebraMap, MFFGen.pull_baseToFunctionField_map g hgs 𝔐.toBase 𝔐.toBase σr hg₂ c,
      RingEquiv.symm_apply_eq]
    exact (𝔐.ffEquiv_algebraMap _).symm
  let Ws : SemilinearAut (AlgebraicClosure ℚ) Fbar :=
    ⟨(Wr, (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)), fun c => hWconst c⟩
  have hWs_smul : ∀ z : Fbar, Ws • z = Wr z := fun z => rfl
  have hWs_base : SemilinearAut.baseAut Ws = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) := rfl

  have hpt : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      (𝔐.pointEquivPlace.symm (gal σ • P)).1 ≫ g = Spec.map (CommRingCat.ofHom σr) ≫ (𝔐.pointEquivPlace.symm P).1 := by
    intro P
    obtain ⟨E, hEpb, hEiso⟩ := tw.gal_rep σ P
    have h1 := pt_pullback _ _ σr sbar sbar (hsb σr) (tw.rep P) E hEpb
    have h2 := pt_iso _ sbar _ _ hEiso
    rw [h2, tw.pt_rep, tw.pt_rep] at h1

    rw [← cancel_mono e𝔐]
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc]
      rw [hg₁]
      exact h1
    · simp only [Category.assoc]
      rw [he𝔐, hg₂, ← Category.assoc, (𝔐.pointEquivPlace.symm (gal σ • P)).2, (𝔐.pointEquivPlace.symm P).2,
        Category.id_comp, Category.comp_id]
  have hcl : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      g.base (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm (gal σ • P))).1 =
        (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm P)).1 := by
    intro P
    show g.base ((𝔐.pointEquivPlace.symm (gal σ • P)).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) =
        (𝔐.pointEquivPlace.symm P).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))
    have h1 : g.base ((𝔐.pointEquivPlace.symm (gal σ • P)).1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) =
        ((𝔐.pointEquivPlace.symm (gal σ • P)).1 ≫ g).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
    have h2 : (Spec.map (CommRingCat.ofHom σr) ≫ (𝔐.pointEquivPlace.symm P).1).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
        (𝔐.pointEquivPlace.symm P).1.base ((Spec.map (CommRingCat.ofHom σr)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) := by
      rw [Scheme.Hom.comp_base, TopCat.comp_app]
    have h3 : (Spec.map (CommRingCat.ofHom σr)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) =
        IsLocalRing.closedPoint (AlgebraicClosure ℚ) := Subsingleton.elim _ _
    rw [h1, hpt P, h2, h3]

  have hplace : ∀ P : Place (AlgebraicClosure ℚ) Fbar, P = 𝔐.placeOfPoint (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm P)) := by
    intro P
    conv_lhs => rw [← 𝔐.pointEquivPlace.apply_symm_apply P]
    exact AlgebraicCurve.CurveModel.pointEquivPlace_apply 𝔐 _
  have hxy : ∀ x₁ x₂ : 𝔐.C, x₁ = x₂ →
      ((algebraMap (𝔐.C.presheaf.stalk x₁) 𝔐.C.functionField).range : Set 𝔐.C.functionField) =
        ((algebraMap (𝔐.C.presheaf.stalk x₂) 𝔐.C.functionField).range : Set 𝔐.C.functionField) := by
    rintro x₁ x₂ rfl; rfl
  have hVS : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      (P.toValuationSubring : Set Fbar) =
        𝔐.ffEquiv.symm '' ((algebraMap (𝔐.C.presheaf.stalk (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm P)).1)
          𝔐.C.functionField).range : Set _) := by
    intro P
    have h := 𝔐.range_stalk_eq (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm P))
    rw [← hplace P] at h
    ext z
    have hz : z ∈ (P.toValuationSubring : Set Fbar) ↔
        z ∈ ((𝔐.ffEquiv.symm : 𝔐.C.functionField ≃+* Fbar).toRingHom.comp
          (algebraMap (𝔐.C.presheaf.stalk (pointEquivClosedPoint 𝔐.toBase (𝔐.pointEquivPlace.symm P)).1)
            𝔐.C.functionField)).range := by
      rw [h]; rfl
    rw [hz]
    simp only [RingHom.mem_range, RingHom.coe_comp, Function.comp_apply, Set.mem_image, SetLike.mem_coe,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨_, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨w, rfl⟩, rfl⟩; exact ⟨w, rfl⟩
  have hWimg : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
      Wr '' (P.toValuationSubring : Set Fbar) = ((gal σ • P).toValuationSubring : Set Fbar) := by
    intro P
    rw [hVS P, hVS (gal σ • P), ← Set.image_comp]
    have : (⇑Wr ∘ ⇑𝔐.ffEquiv.symm) = ⇑𝔐.ffEquiv.symm ∘ ⇑Eg := by
      funext y; simp [hWr, hEg]
    rw [this, Set.image_comp, hxy _ _ (hcl P).symm]
    congr 1
    exact MFFGen.FunctionFieldPull.image_equivOfIso_range_stalk (asIso g) _
  have hWplace : ∀ P : Place (AlgebraicClosure ℚ) Fbar, Ws • P = gal σ • P := by
    intro P
    apply AlgebraicCurve.Place.ext
    apply SetLike.coe_injective
    rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, ValuationSubring.coe_pointwise_smul, ← Set.image_smul, ← hWimg P]
    congr 1

  have hrig : (gal σ)⁻¹ * Ws = 1 := by
    apply AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq Fbar
    · intro c
      show ((SemilinearAut.baseAut (gal σ))⁻¹ * SemilinearAut.baseAut Ws) c = c
      rw [tw.gal_base, hWs_base]; simp
    · intro c; rfl
    · intro P
      rw [mul_smul, hWplace, inv_smul_smul, one_smul]
  have hWeq : Ws = gal σ := by
    have := congrArg (fun w => gal σ * w) hrig
    simpa using this

  have key := MFFGen.FunctionFieldPull.pull_germ g hgs U hU sec
  rw [hsec] at key
  have : MFFGen.FunctionFieldPull.pull g hgs (𝔐.ffEquiv x) = 𝔐.ffEquiv (gal σ • x) := by
    rw [← hWeq, hWs_smul, hWr, RingEquiv.apply_symm_apply]
  exact key.symm.trans this

end S_CerednikDrinfeld_QM_ModuliTowerWitnessD_germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_ModuliTowerWitnessD_germ_app_eq_ffEquiv_gal_smul_of_comp_fst_eq_of_comp_toBase_eq (solution)
