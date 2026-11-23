-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.SF_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:18.013508+00:00
-- url     : https://prove2.me/submissions/590c7fd5-8d98-4c1e-b07c-a71739bca6c7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.MeasureShiftInvariance
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution {S : Set G} {Ω : Set G} (h : SF S Ω) (y : G) : SF S {r | r * y ∈ Ω} := by
  refine ⟨h.1.preimage (measurable_mul_const y), fun x => ?_, fun x hx s hs hsx => ?_⟩
  · obtain ⟨s, hs, hsx⟩ := h.2.1 (x * y)
    exact ⟨s, hs, by simpa [Set.mem_setOf_eq, mul_assoc] using hsx⟩
  · exact h.2.2 (x * y) hx s hs (by simpa [Set.mem_setOf_eq, mul_assoc] using hsx)
end Formalism.L2.SG.MeasureShiftInvariance
