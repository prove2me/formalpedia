-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.graphMorphismToAffineSpace_eq_homOfVector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:16.363742+00:00
-- url     : https://prove2.me/submissions/86e20e44-5d6f-4d4b-b1cf-f99720138f5e

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (D : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
    graphMorphismToAffineSpace k M n q F D =
      AffineSpace.homOfVector
        (D.ι ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin M ⊕ Fin n)))
        (fun i =>
          Sum.elim
            (fun a : Fin M =>
              (ConcreteCategory.hom (Scheme.Hom.appTop D.ι))
                (AffineSpace.coord (Spec (CommRingCat.of k))
                  (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n))))
            (fun j : Fin q => (ConcreteCategory.hom (Scheme.Hom.appTop D.ι)) (F j))
            i.down) :=
  rfl
end FunctorialResolution.EmbeddedResolution
