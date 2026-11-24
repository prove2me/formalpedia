-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weightZeroProj_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:28.520144+00:00
-- url     : https://prove2.me/submissions/2c27cfe9-be34-44cb-bf95-917ad27648ba

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
theorem _root_.solution (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (φ : U →ₗ[K] V) (c : Fin n) :
    homAct G₁.E G₂.E c c (pr0 G₁ G₂ S φ) = 0 := by
  ext x
  have hd : dl c c = 0 := sub_self _
  change G₂.E c c (pr0 G₁ G₂ S φ x) - pr0 G₁ G₂ S φ (G₁.E c c x) = 0
  rw [scalar_projection_apply, scalar_projection_apply, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [G₂.diag, G₁.shift, hd, sub_zero, G₁.diag, map_smul, map_smul]
end Formalism.InvariantFactorPaths.PW
