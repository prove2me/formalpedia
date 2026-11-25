-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ord_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:09.716435+00:00
-- url     : https://prove2.me/submissions/a37889a0-6b31-4928-93d6-ed8f67676e44

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coe_ep
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_of_mem
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_pow

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
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution {ϖ ϖ' : O} (ζ : Pts O A) [IsDVRAt ζ] (h : IsUnif A ϖ) (h' : IsUnif A ϖ')
    (x : A) : ord ϖ ζ x = ord ϖ' ζ x := by
  obtain ⟨n, hn⟩ := h.denom x
  have hm : algebraMap O A ϖ ∈ As O A := (algebraMap O ↥(As O A) ϖ).2
  have hm' : (⟨algebraMap O A ϖ, hm⟩ : ↥(As O A)) = algebraMap O ↥(As O A) ϖ := rfl
  have key : ∀ ϖ'' : O, IsUnif A ϖ'' → ord ϖ'' ζ (ϖ ^ n • x)
      = (((n : ℤ) * (ep ϖ ζ : ℤ) : ℤ) : WithTop ℤ) + ord ϖ'' ζ x := by
    intro ϖ'' h''
    rw [Algebra.smul_def, map_pow, ord_mul ζ h'', ord_pow ζ h'', ord_of_mem ζ h'' hm, hm',
      ← coe_ep ζ h, ENat.map_natCast, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have h1 : ord ϖ ζ (ϖ ^ n • x) = ord ϖ' ζ (ϖ ^ n • x) := by
    rw [ord_of_mem ζ h hn, ord_of_mem ζ h' hn]
  rw [key ϖ h, key ϖ' h'] at h1
  exact (WithTop.add_left_inj WithTop.coe_ne_top).1 h1
end Formalism.MainNotions.Gaps.EtaleWeightGaps
