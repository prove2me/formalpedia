-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.mem_ball_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:53.3782+00:00
-- url     : https://prove2.me/submissions/817501b7-a661-42a8-9ba6-64122814ee03

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_nonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordV_zero
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordV_smul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordV_add

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
variable {V : Type*} [AddCommGroup V] [Module A V]
variable {ϖ : O} {e : V} (c : Pts O A → ℤ)
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e) (v : V) :
    v ∈ ball ϖ e c ↔ ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e c v := by
  refine ⟨fun hv => ?_, fun hv => Submodule.subset_span hv⟩
  induction hv using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => intro ζ; rw [ordV_zero c ζ h he]; exact le_top
  | add x y _ _ hx hy => exact fun ζ => (le_min (hx ζ) (hy ζ)).trans (ordV_add c ζ h he x y)
  | smul a x _ hx =>
    intro ζ
    have : a • x = (a : A) • x := rfl
    rw [this, ordV_smul c ζ h he]
    exact add_nonneg (ord_nonneg ζ h a.2) (hx ζ)
end Formalism.MainNotions.Gaps.EtaleWeightGaps
