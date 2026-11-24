-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.center_nontrivialIndex_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:12.424802+00:00
-- url     : https://prove2.me/submissions/d69d41d2-478c-48ba-83b2-9e8c3cb88f8f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_RemoveIsoBlowups
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowups_center_nontrivialIndex_ne_top_or_length_le

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
theorem _root_.solution (s : SequenceOfBlowups X) {j : ℕ} (h : j < s.lengthWithoutIsoBlowups) :
    s.center (s.nontrivialIndex j) ≠ ⊤ := by
  rcases s.center_nontrivialIndex_ne_top_or_length_le j with hc | hc
  · exact hc
  · exact absurd hc (not_le.mpr (s.nontrivialIndex_lt_length h))
end FunctorialResolution.EmbeddedResolution.SequenceOfBlowups
