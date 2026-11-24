-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.center_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:34.14089+00:00
-- url     : https://prove2.me/submissions/1d441fb2-3c17-4555-a339-2f38aca9dab4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_IdealBlowupSequence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_SequenceIsomorphism
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_PullbackBlowupSequenceComposition

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
open FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
namespace FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} {g : X' ⟶ X}
    {t : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsStrictPullbackBlowupSeq g t s) (i : ℕ) (hi : i < s.length)
    (hs : s.center i = ⊤) : t.center i = ⊤ := by
  obtain ⟨hlen, σ, -, -, hcen⟩ := h
  have hi' : i < t.length := by omega
  rw [hcen i hi', hs, Scheme.IdealSheafData.comap_top]
end FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq
