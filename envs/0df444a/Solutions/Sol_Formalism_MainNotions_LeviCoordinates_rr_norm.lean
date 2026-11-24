-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:32:22.834028+00:00
-- url     : https://prove2.me/submissions/d73ab534-bf35-4265-bb01-d03ac4672a6c

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_map

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
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] (h : rr_FD μ Γ D)
    (hR : rr_IsReg μ Γ D R) (g : G) (F : Lp ℂ 2 (μ.restrict D)) : ‖R g F‖ = ‖F‖ := by
  obtain ⟨hae, hmap⟩ := rr_map h g
  have hF : AEStronglyMeasurable (F : G → ℂ)
      (Measure.map (fun x => rr_rep (Γ : Set G) D (x * g)) (μ.restrict D)) := by
    rw [hmap]; exact Lp.aestronglyMeasurable F
  have key := eLpNorm_map_measure (p := 2) hF hae
  rw [hmap] at key
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hR g F)]
  exact congrArg ENNReal.toReal key.symm
end Formalism.MainNotions.LeviCoordinates
