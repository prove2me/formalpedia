-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartPullback_coordTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:40.664003+00:00
-- url     : https://prove2.me/submissions/cd676641-54c1-44be-9d39-6348944b4bd4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {q : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
private theorem appTop_comp_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : C.presheaf.obj (op ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (c₁ c₂ : EtaleChart q V n) (j : Fin n) :
    (pullback.fst c₁.map c₂.map).appTop.hom (c₁.coordTop j) =
      (pullback.snd c₁.map c₂.map).appTop.hom (c₂.coordTop j) := by
  have h : (pullback.fst c₁.map c₂.map ≫ c₁.map).appTop.hom (affineSpaceCoord k n j)
      = (pullback.snd c₁.map c₂.map ≫ c₂.map).appTop.hom (affineSpaceCoord k n j) := by
    rw [pullback.condition]
  rw [appTop_comp_apply, appTop_comp_apply] at h
  exact h
end FunctorialResolution.EmbeddedResolution
