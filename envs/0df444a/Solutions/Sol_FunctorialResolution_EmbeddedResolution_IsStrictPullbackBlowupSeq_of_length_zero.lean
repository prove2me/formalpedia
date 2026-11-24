-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.of_length_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:02.592328+00:00
-- url     : https://prove2.me/submissions/19e9692c-0834-4140-95f4-90fa00753e13

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations

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
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
namespace IsStrictPullbackBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} (g : X' ⟶ X) (t : SequenceOfBlowups X')
    (s : SequenceOfBlowups X) (ht : t.length = 0) (hs : s.length = 0) :
    IsStrictPullbackBlowupSeq g t s := by
  refine ⟨ht.trans hs.symm,
    fun i hi => schemeAtHomOfEqZero g t s i (Nat.eq_zero_of_le_zero (le_of_le_of_eq hi ht)),
    ?_, ?_, ?_⟩
  · simp [schemeAtHomOfEqZero]
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)
  · intro i hi
    exact absurd (lt_of_lt_of_eq hi ht) (Nat.not_lt_zero i)
end IsStrictPullbackBlowupSeq
end FunctorialResolution.EmbeddedResolution
