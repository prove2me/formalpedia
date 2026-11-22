-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_rep_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:06:28.707436+00:00
-- url     : https://prove2.me/submissions/8fd70384-10a8-4327-b96a-438bb57c2568

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_spec
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_eq
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_N_smul

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
theorem _root_.solution (h : rr_FD μ Γ D) {y c : G} (hc : c ∈ Γ) (hy : y ∉ rr_N Γ D) :
    rr_rep (Γ : Set G) D (c * y) = rr_rep (Γ : Set G) D y := by
  obtain ⟨γ, hγ, he, hD⟩ := rr_rep_spec h y
  have hD' : γ * c⁻¹ * (c * y) ∈ D := by
    rwa [mul_assoc, inv_mul_cancel_left]
  rw [rr_rep_eq h (rr_N_smul hc hy) (Γ.mul_mem hγ (Γ.inv_mem hc)) hD', he,
    mul_assoc, inv_mul_cancel_left]
end Formalism.MainNotions.LeviCoordinates
