-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weightZeroProj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:02.220807+00:00
-- url     : https://prove2.me/submissions/20074514-ae39-45ef-9839-655d0d8e2ca4

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_scalar_projection_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K U V : Type} [Field K] [CharZero K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) {W : Submodule K V} (hW : G₂.Graded W)
    {φ : U →ₗ[K] V} (hφ : ∀ x, φ x ∈ W) (x : U) : pr0 G₁ G₂ S φ x ∈ W := by
  rw [scalar_projection_apply]
  exact Submodule.sum_mem _ fun ν _ => hW ν _ (hφ _)
end Formalism.InvariantFactorPaths.PW
