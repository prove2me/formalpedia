-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.unif_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:57.624559+00:00
-- url     : https://prove2.me/submissions/78856fcb-c6ba-4c0a-bfcc-d79cc2576e21

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]
variable {O A}
attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR
variable {ϖ : O}
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (h : IsUnif A ϖ) :
    algebraMap O ↥(As O A) ϖ ∈ nonZeroDivisors ↥(As O A) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro b hb
  have h1 : (b : A) * algebraMap O A ϖ = 0 := by
    have := congrArg (Subtype.val) hb
    simpa using this
  exact Subtype.ext (by simpa using (h.isUnit.mul_left_eq_zero).1 h1)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
