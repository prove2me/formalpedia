-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_rep_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:34.114802+00:00
-- url     : https://prove2.me/submissions/69fb51c3-b0b5-4b7d-9aa5-b67f8490bb03

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
theorem _root_.solution [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D) {r : G → G}
    (hr : ∀ y, ∃ γ ∈ Γ, r y = γ * y ∧ γ * y ∈ D) (g : G) :
    ∀ᵐ x ∂μ, rr_rep (Γ : Set G) D (x * g) = r (x * g) := by
  have hM : μ ((fun x => x * g) ⁻¹' rr_N Γ D) = 0 := by
    rw [measure_preimage_mul_right]; exact rr_N_null h
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hM
  by_contra hxM
  obtain ⟨γ, hγ, hrx, hD⟩ := hr (x * g)
  exact hx (by rw [hrx]; exact rr_rep_eq (y := x * g) h hxM hγ hD)
end Formalism.MainNotions.LeviCoordinates
