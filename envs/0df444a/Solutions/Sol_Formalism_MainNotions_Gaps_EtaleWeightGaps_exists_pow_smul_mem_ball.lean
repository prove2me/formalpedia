-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.exists_pow_smul_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:16:45.056704+00:00
-- url     : https://prove2.me/submissions/eebcccca-eac1-4d66-9aa3-cb436e0cd083

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_nonneg
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_unif
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_mul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ord_pow
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_ordV_smul
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_mem_ball_iff
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_le_mul_ep

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
variable {V : Type*} [AddCommGroup V] [Module A V] {ϖ : O} {e : V} (c : Pts O A → ℤ)
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) (he : IsGen A e)
    {N : ℕ} (hc : ∀ ζ, -(N : ℤ) ≤ c ζ) (v : V) :
    ∃ k : ℕ, (algebraMap O A ϖ) ^ k • v ∈ ball ϖ e c := by
  obtain ⟨n, hn⟩ := h.denom (coord e v : A)
  refine ⟨N + n, ?_⟩
  rw [mem_ball_iff c h he]
  intro ζ
  have h1 : 0 ≤ ord ϖ ζ ((algebraMap O A ϖ) ^ n) + ord ϖ ζ (coord e v : A) := by
    have := ord_nonneg ζ h hn
    rwa [Algebra.smul_def, map_pow, ord_mul ζ h] at this
  have h2 : 0 ≤ ord ϖ ζ ((algebraMap O A ϖ) ^ N) + ((c ζ : ℤ) : WithTop ℤ) := by
    rw [ord_pow ζ h, ord_unif ζ h, ← WithTop.coe_nsmul, nsmul_eq_mul, ← WithTop.coe_add,
      ← WithTop.coe_zero, WithTop.coe_le_coe]
    have := le_mul_ep ζ h N
    have := hc ζ
    linarith
  rw [ordV_smul c ζ h he, pow_add, ord_mul ζ h, ordV, add_comm (ord ϖ ζ (coord e v : A)),
    add_add_add_comm]
  exact add_nonneg h2 h1
end Formalism.MainNotions.Gaps.EtaleWeightGaps
