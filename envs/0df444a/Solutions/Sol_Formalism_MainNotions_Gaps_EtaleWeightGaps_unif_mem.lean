-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.unif_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:43:57.392299+00:00
-- url     : https://prove2.me/submissions/5f20233e-f9a7-4281-8f16-f10974309804

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
theorem _root_.solution (h : IsUnif A ϖ) (ζ : Pts O A) : algebraMap O ↥(As O A) ϖ ∈ ζ.asIdeal := by
  rw [← Ideal.mem_comap, comap_eq_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  exact h.irreducible.not_isUnit
end Formalism.MainNotions.Gaps.EtaleWeightGaps
