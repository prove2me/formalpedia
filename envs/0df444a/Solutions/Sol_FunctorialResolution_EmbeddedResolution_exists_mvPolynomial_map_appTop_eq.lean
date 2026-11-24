-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_mvPolynomial_map_appTop_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:04.697008+00:00
-- url     : https://prove2.me/submissions/c3ccbaad-c3dc-40b2-87aa-3f65ff231bed

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_ExtendCoordinatesToAffineSpace
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceProduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PolynomialRingOverGlobalSections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
private theorem appTop_surjective_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsClosedImmersion f] :
    Function.Surjective ⇑((f.appTop).hom) :=
  (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine (f := f)).2
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] (A : Scheme.{u}) (M : ℕ)
    (e : A ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin M)))
    [AlgebraicGeometry.IsClosedImmersion e] (n q : ℕ)
    (rel : Fin q → MvPolynomial (Fin n) Γ(A, ⊤)) (j : Fin q) :
    ∃ P : MvPolynomial (Fin n) Γ(affineSpaceIndexedBy k (ULift.{u} (Fin M)), ⊤),
      MvPolynomial.map (e.appTop).hom P = rel j := by
  obtain ⟨P, hP⟩ := MvPolynomial.map_surjective ((e.appTop).hom)
    (appTop_surjective_of_isClosedImmersion e) (rel j)
  exact ⟨P, hP⟩
end FunctorialResolution.EmbeddedResolution
