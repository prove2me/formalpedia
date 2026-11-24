-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.center_nextNontrivialIndex_ne_top_or_length_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:42:25.859803+00:00
-- url     : https://prove2.me/submissions/81a86784-893d-4441-8a34-e59ecfeeab33

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups

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
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
theorem _root_.solution (s : SequenceOfBlowups X) (a : ℕ) :
    s.center (s.nextNontrivialIndex a) ≠ ⊤ ∨ s.length ≤ s.nextNontrivialIndex a :=
  (s.nextNontrivialIndex_spec a).2
end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
