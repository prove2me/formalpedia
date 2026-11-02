-- Prove2me | solution 1 for ConcreteSheaves.Quasitopos.proposition_50
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:52:02.406036+00:00
-- url     : https://prove2.me/submissions/04e034dd-4aeb-4516-a838-3566d519d5be

import Theorems.Thm_ConcreteSheaves_Quasitopos_lemma_47
import Theorems.Thm_ConcreteSheaves_Quasitopos_lemma_49
import Mathlib.CategoryTheory.Monad.Limits

open CategoryTheory CategoryTheory.Limits ConcreteSheaves.Quasitopos Opposite

universe u
variable {D : Type u} [SmallCategory D]

theorem solution (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    HasColimits (DSpace K T) := by
  classical
  let J := K.toGrothendieck
  let R := (IsDSpace K T).ι
  let F : (Dᵒᵖ ⥤ Type u) → DSpace K T := fun P =>
    ⟨J.plusObj (concretization T P),
      lemma_49 K T hT hK _ (lemma_47 K T hT hK P).1⟩
  let η (P : Dᵒᵖ ⥤ Type u) : P ⟶ (F P).obj :=
    concretizationπ T P ≫ J.toPlus (concretization T P)
  have sheaf (Q : DSpace K T) : Presheaf.IsSheaf J Q.obj := by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
    intro X S hS
    exact Q.property.1 S hS
  have hu (P : Dᵒᵖ ⥤ Type u) (Q : DSpace K T) (f : P ⟶ Q.obj) :
      ∃! g : F P ⟶ Q, η P ≫ g.hom = f := by
    obtain ⟨g₀, hg₀, unique⟩ := (lemma_47 K T hT hK P).2 Q.obj Q.property.2 f
    refine ⟨ObjectProperty.homMk (J.plusLift g₀ (sheaf Q)), ?_, ?_⟩
    · dsimp [η]
      rw [Category.assoc, J.toPlus_plusLift, hg₀]
    · intro g hg
      apply ObjectProperty.hom_ext
      apply J.plus_hom_ext _ _ (sheaf Q)
      change J.toPlus (concretization T P) ≫ g.hom =
        J.toPlus (concretization T P) ≫ J.plusLift g₀ (sheaf Q)
      rw [J.toPlus_plusLift]
      apply unique
      simpa only [η, Category.assoc] using hg
  let e (P : Dᵒᵖ ⥤ Type u) (Q : DSpace K T) :
      (F P ⟶ Q) ≃ (P ⟶ R.obj Q) :=
    Equiv.ofBijective (fun g => η P ≫ g.hom) (by
      constructor
      · intro a b hab
        obtain ⟨g, hg, huniq⟩ := hu P Q (η P ≫ a.hom)
        exact (huniq a rfl).trans (huniq b hab.symm).symm
      · intro f
        obtain ⟨g, hg, _⟩ := hu P Q f
        exact ⟨g, hg⟩)
  have he : ∀ P Q Q' g h, e P Q' (h ≫ g) = e P Q h ≫ R.map g := by
    intro P Q Q' g h
    change η P ≫ (h.hom ≫ g.hom) = (η P ≫ h.hom) ≫ g.hom
    exact (Category.assoc _ _ _).symm
  let : Reflective R :=
    { L := Adjunction.leftAdjointOfEquiv e he
      adj := Adjunction.adjunctionOfEquivLeft e he }
  exact hasColimits_of_reflective R
