-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:31:30.56382+00:00
-- url     : https://prove2.me/submissions/759ee295-39ea-4a5c-b7f7-c3abe42b068a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_eq
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordAt_mul

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
variable (ζ : Pts O A) [IsDVRAt ζ]
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (h : IsUnif A ϖ) (x y : A) : ord ϖ ζ (x * y) = ord ϖ ζ x + ord ϖ ζ y := by
  obtain ⟨n, hn⟩ := h.denom x
  obtain ⟨m, hm⟩ := h.denom y
  have e : ϖ ^ (n + m) • (x * y) = (ϖ ^ n • x) * (ϖ ^ m • y) := by
    rw [smul_mul_smul_comm, pow_add]
  have hnm : ϖ ^ (n + m) • (x * y) ∈ As O A := e ▸ (As O A).mul_mem hn hm
  rw [ord_eq ζ h hn, ord_eq ζ h hm, ord_eq ζ h hnm, ← ordAt_mul]
  congr 1
  exact Subtype.ext e
end Formalism.MainNotions.Gaps.EtaleWeightGaps
