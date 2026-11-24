-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_FD_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:41:37.73945+00:00
-- url     : https://prove2.me/submissions/a6df1952-1583-42ed-9dbc-c1a3a2925196

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep

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
theorem _root_.solution [μ.IsMulRightInvariant] (h : rr_FD μ Γ D) (g : G) : rr_FD μ Γ ((fun x => x * g) ⁻¹' D) where
  meas := (measurable_mul_const g) h.meas
  cov := fun y => by
    obtain ⟨γ, hγ, hD⟩ := h.cov (y * g)
    exact ⟨γ, hγ, by simpa [mul_assoc] using hD⟩
  disj := fun γ hγ h1 => by
    have : (fun y => γ * y) '' ((fun x => x * g) ⁻¹' D) ∩ (fun x => x * g) ⁻¹' D ⊆
        (fun x => x * g) ⁻¹' ((fun y => γ * y) '' D ∩ D) := by
      rintro _ ⟨⟨y, hy, rfl⟩, h2⟩
      exact ⟨⟨y * g, hy, by simp [mul_assoc]⟩, h2⟩
    refine measure_mono_null this ?_
    rw [measure_preimage_mul_right]
    exact h.disj γ hγ h1
end Formalism.MainNotions.LeviCoordinates
