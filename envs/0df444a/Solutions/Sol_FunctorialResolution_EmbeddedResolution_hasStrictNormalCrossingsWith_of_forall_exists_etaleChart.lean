-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_of_forall_exists_etaleChart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:28.015911+00:00
-- url     : https://prove2.me/submissions/ba03aa92-aeaf-464b-af7e-2a899d412997

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData}
    {E : List X.IdealSheafData}
    (h : ∀ x ∈ Z.support,
      ∃ (U : X.Opens) (_ : x ∈ U) (m : ℕ) (c : EtaleChart p U m) (a : ℕ → Option (Fin m))
        (S : Finset (Fin m)),
        (∀ i < E.length, ∀ j < E.length, ∀ t : Fin m, a i = some t → a j = some t → i = j) ∧
        (∀ i, ∀ h : i < E.length, a i = none → restrictIdeal (E[i]'h) U = ⊤) ∧
        (∀ i, ∀ h : i < E.length, ∀ t : Fin m, a i = some t →
          restrictIdeal (E[i]'h) U = c.coordIdeal {t}) ∧
        restrictIdeal Z U = c.coordIdeal S) :
    HasStrictNormalCrossingsWith p Z E :=
  h
end FunctorialResolution.EmbeddedResolution
