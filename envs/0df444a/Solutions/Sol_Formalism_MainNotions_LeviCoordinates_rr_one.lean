-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rr_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:00:07.540724+00:00
-- url     : https://prove2.me/submissions/278de7ed-bb9f-4d60-8f54-f2c92acabf1a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrExistsMeasRep
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rr_rep_self

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
theorem _root_.solution [μ.IsMulLeftInvariant] [Countable Γ] (h : rr_FD μ Γ D) (hR : rr_IsReg μ Γ D R) : R 1 = 1 := by
  ext F : 1
  refine Lp.ext ?_
  rw [ContinuousLinearMap.one_apply]
  filter_upwards [hR 1 F, rr_rep_self h] with x e1 e2
  simp only [e1, e2]
end Formalism.MainNotions.LeviCoordinates
