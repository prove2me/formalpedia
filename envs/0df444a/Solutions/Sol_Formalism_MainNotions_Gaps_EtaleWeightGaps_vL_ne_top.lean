-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.vL_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:11.735526+00:00
-- url     : https://prove2.me/submissions/3d26f265-11db-4f34-b321-47e4b6a79534

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_vL_eq_top_iff

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
variable (ζ : Pts O A) [IsDVRAt ζ]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution {a : ↥(As O A)} (ha : a ∈ nonZeroDivisors ↥(As O A)) : vL ζ a ≠ ⊤ := by
  rw [Ne, vL_eq_top_iff, IsLocalization.map_eq_zero_iff ζ.asIdeal.primeCompl]
  rintro ⟨⟨m, hm⟩, h⟩
  have : m = 0 := (mem_nonZeroDivisors_iff_right.1 ha) m h
  exact hm (this ▸ ζ.asIdeal.zero_mem)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
