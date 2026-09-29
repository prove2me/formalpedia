-- Prove2me | solution 1 for CategoryTheory.MonoidalClosed.isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9bb17da8-f0d3-5358-af22-7bffab7b158a

import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit

set_option autoImplicit false

universe v u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace ReflSol

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.defeqAttrib.useBackward true in
noncomputable def tensorLeftEquiv {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft M) (tensorLeft N)
    (NatIso.ofComponents
      (fun X => (λ_ X).symm ≪≫ (whiskerRightIso ((β_ N M) ≪≫ e).symm X) ≪≫ α_ N M X)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, associator_naturality_right]))
    (NatIso.ofComponents
      (fun X => (α_ M N X).symm ≪≫ whiskerRightIso e X ≪≫ λ_ X)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality]))

set_option backward.defeqAttrib.useBackward true in
noncomputable def tensorRightEquiv {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight N) (tensorRight M)
    (NatIso.ofComponents
      (fun X => (ρ_ X).symm ≪≫ (whiskerLeftIso X ((β_ N M) ≪≫ e).symm) ≪≫ (α_ X N M).symm)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, associator_inv_naturality_left]))
    (NatIso.ofComponents
      (fun X => α_ X M N ≪≫ whiskerLeftIso X e ≪≫ ρ_ X)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]))

noncomputable def tensorLeftAdj {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : tensorLeft M ⊣ tensorLeft N :=
  (tensorLeftEquiv e).toAdjunction

theorem isIso_tensorLeftAdj_counit_app {M N : C} (e : M ⊗ N ≅ 𝟙_ C) (X : C) :
    IsIso ((tensorLeftAdj e).counit.app X) := by
  change IsIso ((tensorLeftEquiv e).counitIso.hom.app X)
  infer_instance

noncomputable def tensorRightFF {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : (tensorRight N).FullyFaithful :=
  (tensorRightEquiv e).fullyFaithfulFunctor

variable [MonoidalClosed C]

theorem isIso_ev_app {M N : C} (e : M ⊗ N ≅ 𝟙_ C) (X : C) : IsIso ((ihom.ev M).app X) := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit (ihom.adjunction M) (tensorLeftAdj e) X

  have h' : (ihom.ev M).app X =
      (tensorLeft M).map (((ihom.adjunction M).rightAdjointUniq (tensorLeftAdj e)).hom.app X) ≫
        (tensorLeftAdj e).counit.app X := by
    rw [h]; rfl
  rw [h']
  haveI h1 : IsIso (((ihom.adjunction M).rightAdjointUniq (tensorLeftAdj e)).hom.app X) := inferInstance
  have h2 : IsIso ((tensorLeft M).map (((ihom.adjunction M).rightAdjointUniq (tensorLeftAdj e)).hom.app X)) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' h2 (isIso_tensorLeftAdj_counit_app e X)

theorem isIso_toBidual {M N : C} (e : M ⊗ N ≅ 𝟙_ C) :
    IsIso (MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))) := by

  let e' : M ⊗ (ihom M).obj (𝟙_ C) ≅ 𝟙_ C := @asIso _ _ _ _ ((ihom.ev M).app (𝟙_ C)) (isIso_ev_app e (𝟙_ C))
  have he' : e'.hom = (ihom.ev M).app (𝟙_ C) := rfl
  apply isIso_of_yoneda_map_bijective
  intro T
  have key : ∀ g : T ⟶ M,
      MonoidalClosed.uncurry (g ≫ MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C)))
        = (β_ ((ihom M).obj (𝟙_ C)) T).hom ≫ ((g ▷ (ihom M).obj (𝟙_ C)) ≫ e'.hom) := by
    intro g
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry, he',
      BraidedCategory.braiding_naturality_right_assoc]
  let Φ : (T ⟶ M) ≃ ((ihom M).obj (𝟙_ C) ⊗ T ⟶ 𝟙_ C) :=
    ((tensorRightFF e').homEquiv.trans (Iso.homCongr (Iso.refl _) e')).trans
      (Iso.homCongr (β_ ((ihom M).obj (𝟙_ C)) T).symm (Iso.refl _))
  have hΦ : ∀ g : T ⟶ M, Φ g = MonoidalClosed.uncurry
      (g ≫ MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))) := by
    intro g
    rw [key]
    simp [Φ, Iso.homCongr, Functor.FullyFaithful.homEquiv]
  have hfun : (fun g : T ⟶ M =>
        g ≫ MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C)))
      = fun g => MonoidalClosed.curry (Φ g) := by
    funext g
    exact ((MonoidalClosed.curry_eq_iff _ _).mpr (hΦ g)).symm
  rw [hfun]
  exact (Φ.trans ⟨MonoidalClosed.curry, MonoidalClosed.uncurry, MonoidalClosed.uncurry_curry,
    MonoidalClosed.curry_uncurry⟩).bijective

end ReflSol

theorem solution
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    {M N : C} (e : M ⊗ N ≅ 𝟙_ C) :
    (∀ X : C, IsIso ((ihom.ev M).app X)) ∧
      IsIso (MonoidalClosed.curry
        ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))) :=
  ⟨ReflSol.isIso_ev_app e, ReflSol.isIso_toBidual e⟩

end S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
end P2MW
export P2MW.S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit (solution)
