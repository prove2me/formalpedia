-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_rep_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:38.479173+00:00
-- url     : https://prove2.me/submissions/2af7ffec-7cc4-4f3d-8eee-a1b995ebe901

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_N_null
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_spec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_smul

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
theorem _root_.solution [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) (g k : G) :
    ∀ᵐ x ∂μ, rr_rep (Γ : Set G) D (rr_rep (Γ : Set G) D (x * g) * k) = rr_rep (Γ : Set G) D (x * (g * k)) := by
  have hM : μ ((fun x => x * (g * k)) ⁻¹' rr_N Γ D) = 0 := by
    rw [measure_preimage_mul_right]; exact rr_N_null h
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hM
  by_contra hxM
  obtain ⟨γ, hγ, he, -⟩ := rr_rep_spec h (x * g)
  refine hx ?_
  rw [he, show γ * (x * g) * k = γ * (x * (g * k)) by simp only [mul_assoc]]
  exact rr_rep_smul (y := x * (g * k)) h hγ hxM
end Formalism.MainNotions.LeviCoordinates
