-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.irreducibleComponentsDisjointOfSmooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:41.073856+00:00
-- url     : https://prove2.me/submissions/85d67e03-0223-4d6a-9407-8c55bd336967

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_IrreducibleComponents
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_SmoothComponentsDisjoint
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_irreducibleComponents_eq_of_stalk_isDomain
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isDomain_stalk_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution : IrreducibleComponentsDisjointOfSmooth.{u} := by
  intro k _ X p hp C₁ h₁ C₂ h₂ hne
  have : AlgebraicGeometry.Smooth p := hp
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  exact hne
    (irreducibleComponents_eq_of_stalk_isDomain X
      (fun y => isDomain_stalk_of_smooth p y) h₁ h₂ hx₁ hx₂)
end FunctorialResolution.EmbeddedResolution
