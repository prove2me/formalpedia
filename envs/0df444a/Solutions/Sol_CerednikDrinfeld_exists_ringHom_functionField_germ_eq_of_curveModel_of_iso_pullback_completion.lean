-- Prove2me | solution 1 for CerednikDrinfeld.exists_ringHom_functionField_germ_eq_of_curveModel_of_iso_pullback_completion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/5cdf9384-8d14-5952-aad4-3682b983e110

import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Mathlib
import Theorems.Thm_AlgebraicGeometry_functionField_pullback_generates_and_linearIndependent
import Theorems.Thm_AlgebraicGeometry_genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_ringHom_functionField_germ_eq_of_curveModel_of_iso_pullback_completion
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicGeometry

open CategoryTheory.Limits AlgebraicCurve

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

end MFFGen

end

set_option maxHeartbeats 3200000 in

theorem solution
    (R : Type) [CommRing R]
    (A₂ : ValuationSubring (AlgebraicClosure ℚ))
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of R))

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (𝒪₀ : Type) [CommRing 𝒪₀] [Algebra 𝒪₀ ↥(ValuationSubring.ratClosure A₂)]
    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    [hXCint : IsIntegral (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))]

    (u : (Limits.pullback πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) ≅ (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))))
    (hu : u.hom ≫ Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))) = Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar))
    :
    ∃ j : Fbar →+* ↑(Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).functionField,

      (∀ (x : Fbar) (U : 𝔐.C.Opens) (hU : (genericPoint (𝔐.C : Scheme.{0})) ∈ U)
        (hU' : (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) ∈ (u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐) ⁻¹ᵁ U)
        (sec : 𝔐.C.presheaf.obj (Opposite.op U)),
        (𝔐.C.presheaf.germ U (genericPoint (𝔐.C : Scheme.{0})) hU).hom sec = 𝔐.ffEquiv x →
        ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))).presheaf.germ ((u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐) ⁻¹ᵁ U) (genericPoint ((Limits.pullback f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))))) : Scheme.{0})) hU').hom (((u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar)) (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom)))) (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐).app U).hom sec) = j x) ∧

      (∀ z : AlgebraicClosure ℚ, j (algebraMap (AlgebraicClosure ℚ) Fbar z) = (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ((z : AlgebraicClosure ℚ) : A₂.valuation.Completion)) ∧

      (Subfield.closure (Set.range (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) ∪ Set.range j) = ⊤) ∧

      (∀ (t : Finset Fbar), LinearIndependent (AlgebraicClosure ℚ) (fun x : t => (x : Fbar)) →
        ∀ c : t → A₂.valuation.Completion, (∑ x : t, (AlgebraicCurve.baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂))))))) (c x) * j (x : Fbar)) = 0 → ∀ x : t, c x = 0) := by
  classical

  let ιC : AlgebraicClosure ℚ →+* A₂.valuation.Completion := (UniformSpace.Completion.coeRingHom.comp ((WithVal.equiv A₂.valuation).symm.toRingHom))
  let τ : 𝒪₀ →+* A₂.valuation.Completion := ((algebraMap ↥(ValuationSubring.ratClosure A₂) A₂.valuation.Completion).comp (algebraMap 𝒪₀ ↥(ValuationSubring.ratClosure A₂)))
  let φ : Limits.pullback f₀ (Spec.map (CommRingCat.ofHom τ)) ⟶ 𝔐.C := u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom ιC) ≫ sbar))
      (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom ιC) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom ιC))
      (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐
  have hφdef : φ = u.inv ≫ Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom ιC) ≫ sbar))
      (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom ιC) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom ιC))
      (by simp only [Category.assoc, Limits.pullback.condition]) ≫ CategoryTheory.inv e𝔐 := rfl
  letI instAlg : Algebra (AlgebraicClosure ℚ) A₂.valuation.Completion := ιC.toAlgebra
  have hιA : algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion = ιC := rfl
  haveI hXk : IsIntegral (Limits.pullback πX sbar) := IsIntegral.of_isIso e𝔐

  let plb := pullbackLeftPullbackSndIso πX sbar
    (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion)))
  let θ : Limits.pullback (Limits.pullback.snd πX sbar)
      (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion))) ≅
      Limits.pullback f₀ (Spec.map (CommRingCat.ofHom τ)) := plb ≪≫ u
  haveI hXC' : IsIntegral (Limits.pullback (Limits.pullback.snd πX sbar)
      (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion)))) :=
    IsIntegral.of_isIso θ.inv
  have hinj : Function.Injective (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion) :=
    (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion).injective

  have h1 : CategoryTheory.inv e𝔐 ≫ 𝔐.toBase = Limits.pullback.snd πX sbar := by
    rw [← he𝔐, IsIso.inv_hom_id_assoc]
  have h2 : u.inv ≫ Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom ιC) ≫ sbar) =
      Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom τ)) := by
    rw [← hu, Iso.inv_hom_id_assoc]
  have hL : Limits.pullback.lift (Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom ιC) ≫ sbar))
      (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom ιC) ≫ sbar) ≫ Spec.map (CommRingCat.ofHom ιC))
      (by simp only [Category.assoc, Limits.pullback.condition]) =
      plb.inv ≫ Limits.pullback.fst _ _ := by
    apply Limits.pullback.hom_ext
    · rw [Limits.pullback.lift_fst, Category.assoc]
      exact (pullbackLeftPullbackSndIso_inv_fst πX sbar _).symm
    · rw [Limits.pullback.lift_snd, Category.assoc]
      exact (pullbackLeftPullbackSndIso_inv_fst_snd πX sbar _).symm
  have hθinv : θ.inv = u.inv ≫ plb.inv := rfl
  have hφeq : φ = θ.inv ≫ Limits.pullback.fst _ _ ≫ CategoryTheory.inv e𝔐 := by
    rw [hφdef, hL, hθinv]; simp only [Category.assoc]
  have hθsnd : θ.symm.hom ≫ Limits.pullback.snd (Limits.pullback.snd πX sbar)
      (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion))) =
      Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom τ)) := by
    rw [Iso.symm_hom, hθinv, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    exact h2
  have hφbase : φ ≫ 𝔐.toBase = Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom τ)) ≫ Spec.map (CommRingCat.ofHom ιC) := by
    rw [hφdef]; simp only [Category.assoc, h1, Limits.pullback.lift_snd]; rw [← Category.assoc, h2]

  have hfst : (Limits.pullback.fst (Limits.pullback.snd πX sbar)
      (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion)))).base
      (genericPoint _) ⤳ genericPoint (Limits.pullback πX sbar : Scheme.{0}) := by
    rw [specializes_iff_forall_open]
    intro U hUo hmem
    have := genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap hinj (Limits.pullback.snd πX sbar)
      (𝟙 _) ⟨U, hUo⟩ ⟨_, hmem⟩
    simpa using this
  have hθs : θ.inv.base (genericPoint _) ⤳ genericPoint _ := MFFGen.FunctionFieldPull.specializes_of_iso_inv θ
  have hes : (CategoryTheory.inv e𝔐).base (genericPoint _) ⤳ genericPoint 𝔐.C :=
    MFFGen.FunctionFieldPull.specializes_of_iso_inv (asIso e𝔐)
  have hφs' : (θ.inv ≫ Limits.pullback.fst _ _ ≫ CategoryTheory.inv e𝔐).base (genericPoint _) ⤳ genericPoint 𝔐.C := by
    rw [specializes_iff_forall_open]
    intro U hUo hmem
    have hne : ((CategoryTheory.inv e𝔐) ⁻¹ᵁ ⟨U, hUo⟩ : Set _).Nonempty := ⟨e𝔐.base (genericPoint 𝔐.C), by
      show (e𝔐 ≫ CategoryTheory.inv e𝔐).base (genericPoint 𝔐.C) ∈ U
      rw [IsIso.hom_inv_id]; exact hmem⟩
    have := genericPoint_mem_preimage_comp_pullback_fst_of_injective_algebraMap hinj (Limits.pullback.snd πX sbar)
      θ.inv _ hne
    exact this
  have hφs : φ.base (genericPoint _) ⤳ genericPoint 𝔐.C := hφeq ▸ hφs'

  let prStar := (MFFGen.FunctionFieldPull.pull (Limits.pullback.fst (Limits.pullback.snd πX sbar)
      (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion)))) hfst).hom
  let E := MFFGen.FunctionFieldPull.equivOfIso θ.symm
  let β : Fbar ≃+* (Limits.pullback πX sbar).functionField :=
    𝔐.ffEquiv.trans (MFFGen.FunctionFieldPull.equivOfIso (asIso e𝔐).symm)
  have hβ : ∀ a, β a = MFFGen.FunctionFieldPull.pull (CategoryTheory.inv e𝔐) hes (𝔐.ffEquiv a) := fun a => rfl
  let j : Fbar →+* (Limits.pullback f₀ (Spec.map (CommRingCat.ofHom τ))).functionField :=
    (MFFGen.FunctionFieldPull.pull φ hφs).hom.comp 𝔐.ffEquiv.toRingHom
  have hjdef : ∀ a, j a = MFFGen.FunctionFieldPull.pull φ hφs (𝔐.ffEquiv a) := fun a => rfl
  have hj : ∀ a, j a = E (prStar (β a)) := by
    intro a
    rw [hjdef, hβ, MFFGen.pull_congr_apply _ _ hφeq hφs hφs',
      MFFGen.pull_comp_apply θ.inv _ hθs (((CategoryTheory.inv e𝔐).base.hom.map_specializes hfst).trans hes),
      MFFGen.pull_comp_apply _ _ hfst hes]
    rfl

  obtain ⟨hGa, hGb⟩ := AlgebraicGeometry.functionField_pullback_generates_and_linearIndependent
    (AlgebraicClosure ℚ) A₂.valuation.Completion (Limits.pullback πX sbar) (Limits.pullback.snd πX sbar) prStar
    (fun U hU hU' sec => MFFGen.FunctionFieldPull.pull_germ _ hfst U hU sec)
  have hb : ∀ c, baseToFunctionField (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom τ))) c =
      E (baseToFunctionField (Limits.pullback.snd (Limits.pullback.snd πX sbar)
        (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) A₂.valuation.Completion)))) c) :=
    fun c => (MFFGen.FunctionFieldPull.equivOfIso_baseToFunctionField θ.symm _ _ hθsnd c).symm
  have hβk : ∀ a, β (algebraMap (AlgebraicClosure ℚ) Fbar a) = baseToFunctionField (Limits.pullback.snd πX sbar) a := by
    intro a
    rw [hβ, 𝔐.ffEquiv_algebraMap]
    exact MFFGen.FunctionFieldPull.pull_baseToFunctionField _ hes _ _ h1 a
  refine ⟨j, ?_, ?_, ?_, ?_⟩
  ·
    intro x U hU hU' sec hsec
    have key := MFFGen.FunctionFieldPull.pull_germ φ hφs U hU sec
    rw [hsec] at key
    exact key.symm.trans (hjdef x).symm
  ·
    intro z
    have e1 := hjdef (algebraMap (AlgebraicClosure ℚ) Fbar z)
    have e2 : 𝔐.ffEquiv (algebraMap (AlgebraicClosure ℚ) Fbar z) = baseToFunctionField 𝔐.toBase z :=
      𝔐.ffEquiv_algebraMap z
    have e3 := MFFGen.pull_baseToFunctionField_map φ hφs
      (Limits.pullback.snd f₀ (Spec.map (CommRingCat.ofHom τ))) 𝔐.toBase ιC hφbase z
    rw [e2] at e1
    exact e1.trans e3
  ·
    exact MFFGen.closure_transfer E _ _ hb prStar β β.surjective j hj hGa
  ·
    intro t ht c hc x
    exact MFFGen.linIndep_transfer β _ hβk E _ _ hb prStar j hj hGb t ht c hc x

end S_CerednikDrinfeld_exists_ringHom_functionField_germ_eq_of_curveModel_of_iso_pullback_completion
end P2MW
export P2MW.S_CerednikDrinfeld_exists_ringHom_functionField_germ_eq_of_curveModel_of_iso_pullback_completion (solution)
