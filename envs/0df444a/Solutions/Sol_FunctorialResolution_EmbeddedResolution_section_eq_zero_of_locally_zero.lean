-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.section_eq_zero_of_locally_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:50:11.252063+00:00
-- url     : https://prove2.me/submissions/7fe41f86-266d-4649-b532-9cfc9ab6831f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReduction_IsomorphismTransport
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_IsoBlowupPushforward

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {X : Scheme.{u}} (U : X.Opens)
    (s : X.presheaf.obj (op U))
    (h : ∀ x ∈ U, ∃ V : X.Opens, ∃ hV : V ≤ U, x ∈ V ∧
      X.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  obtain ⟨V, hV, hxV, hs⟩ := h x hx
  have h1 : X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hV).op s)
      = X.presheaf.germ U x hx s := X.presheaf.germ_res_apply (homOfLE hV) x hxV s
  rw [hs, map_zero] at h1
  show X.presheaf.germ U x hx s = X.presheaf.germ U x hx 0
  rw [map_zero]
  exact h1.symm
end FunctorialResolution.EmbeddedResolution
