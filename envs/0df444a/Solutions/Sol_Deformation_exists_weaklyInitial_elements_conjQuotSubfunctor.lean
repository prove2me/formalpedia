-- Prove2me | solution 1 for Deformation.exists_weaklyInitial_elements_conjQuotSubfunctor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/ac87128d-bcf5-5d99-9da8-7fa8d432ff50

import Mathlib
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor

p2m_open "CategoryTheory P2MW.S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor.CategoryTheory"

namespace CategoryTheory
p2m_export "CategoryTheory" "FunctorToTypes.naturality Category CategoryOfElements.map Subfunctor"
namespace CategoryOfElements
p2m_export "CategoryTheory.CategoryOfElements" "map"
namespace SolAux
p2m_open "CategoryTheory.CategoryOfElements CategoryTheory"

universe w v u
variable {C : Type u} [Category.{v} C] {F₁ F₂ : C ⥤ Type w}

theorem map_obj_weaklyInitial (α : F₁ ⟶ F₂) (hα : ∀ X, Function.Surjective (α.app X))
    {T : F₁.Elements} (hT : ∀ X, Nonempty (T ⟶ X)) (Y : F₂.Elements) :
    Nonempty ((CategoryOfElements.map α).obj T ⟶ Y) := by
  obtain ⟨x, hx⟩ := hα Y.1 Y.2
  obtain ⟨f⟩ := hT (F₁.elementsMk Y.1 x)
  refine ⟨⟨f.1, ?_⟩⟩
  show F₂.map f.1 (α.app T.1 T.2) = Y.2
  rw [← FunctorToTypes.naturality, f.2, hx]

end CategoryTheory.CategoryOfElements.SolAux

universe u

theorem solution (n : Type) [Fintype n] [DecidableEq n] {G : Type u} [Group G]
    [TopologicalSpace G] {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
    {F : CategoryTheory.Subfunctor (Deformation.repnFunctor n G 𝓞)} (T : F.toFunctor.Elements)
    (hT : ∀ (X : F.toFunctor.Elements), Nonempty (T ⟶ X)) :
    ∃ T', ∀ (X : (Deformation.conjQuotSubfunctor n F).toFunctor.Elements), Nonempty (T' ⟶ X) :=
  ⟨(CategoryOfElements.map (Deformation.condLiftToDeformation n F)).obj T,
    CategoryTheory.CategoryOfElements.SolAux.map_obj_weaklyInitial (Deformation.condLiftToDeformation n F)
      (Deformation.condLiftToDeformation_surjective n F) hT⟩

end S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor
end P2MW
export P2MW.S_Deformation_exists_weaklyInitial_elements_conjQuotSubfunctor (solution)
