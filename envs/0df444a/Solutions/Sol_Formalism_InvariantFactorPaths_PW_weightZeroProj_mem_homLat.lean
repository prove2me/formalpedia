-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.weightZeroProj_mem_homLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:50:25.117221+00:00
-- url     : https://prove2.me/submissions/64df318d-424c-4261-a3e9-fd6fbbbf1fd9

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
theorem _root_.solution (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) {L : AddSubgroup U} {M : AddSubgroup V}
    (hL : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L) (hM : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M)
    {φ : U →ₗ[K] V} (hφ : φ ∈ HomLat (K := K) L M) : pr0 G₁ G₂ S φ ∈ HomLat (K := K) L M := by
  have hφ' : ∀ x ∈ L, φ x ∈ M := hφ
  show ∀ x ∈ L, pr0 G₁ G₂ S φ x ∈ M
  intro x hx
  rw [scalar_projection_apply]
  exact AddSubgroup.sum_mem _ fun ν _ => hM ν _ (hφ' _ (hL ν x hx))
end Formalism.InvariantFactorPaths.PW
