-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.ind_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:56.066336+00:00
-- url     : https://prove2.me/submissions/9bde0fde-d56e-44c9-bada-3e5d2e9fb523

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
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
namespace Formalism.L2.SG.MeasureShiftInvariance
theorem _root_.solution {M : Type*} [Zero M] [One M] {B : Set G} (x : G) :
    (fun r => B.indicator (1 : G → M) (r * x)) = {r | r * x ∈ B}.indicator 1 := by
  funext r
  first
  | rfl
  | simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
end Formalism.L2.SG.MeasureShiftInvariance
