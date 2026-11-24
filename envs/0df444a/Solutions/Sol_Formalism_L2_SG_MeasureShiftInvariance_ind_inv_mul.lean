-- Prove2me | solution 1 for Formalism.L2.SG.MeasureShiftInvariance.ind_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:17:54.673782+00:00
-- url     : https://prove2.me/submissions/f9426135-1f0b-47b0-a64b-2ed550e33d4a

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
theorem _root_.solution {M : Type*} [Zero M] [One M] {A : Set G} (y : G) :
    (fun r => A.indicator (1 : G → M) (r⁻¹ * y)) = {r | r⁻¹ * y ∈ A}.indicator 1 := by
  funext r
  first
  | rfl
  | simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
end Formalism.L2.SG.MeasureShiftInvariance
