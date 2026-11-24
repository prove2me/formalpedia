-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_rep_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:39.292318+00:00
-- url     : https://prove2.me/submissions/cb0321b0-d607-4ac0-9f4b-28012abc0cd8

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_N_null
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Set
open scoped ENNReal Pointwise InnerProductSpace
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} {Γ : Subgroup G} {D : Set G}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) :
    ∀ᵐ x ∂μ.restrict D, rr_rep (Γ : Set G) D (x * 1) = x := by
  rw [ae_restrict_iff' h.meas, ae_iff]
  refine measure_mono_null (fun x hx => ?_) (rr_N_null h)
  by_contra hxM
  simp only [Set.mem_setOf_eq, _root_.not_imp] at hx
  obtain ⟨hxD, hne⟩ := hx
  apply hne
  rw [mul_one]
  have e := rr_rep_eq h hxM Γ.one_mem (by rwa [one_mul])
  rwa [one_mul] at e
end Formalism.MainNotions.LeviCoordinates
