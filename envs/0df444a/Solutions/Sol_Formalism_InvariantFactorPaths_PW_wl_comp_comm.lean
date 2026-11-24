-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.wl_comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:50:26.020523+00:00
-- url     : https://prove2.me/submissions/16b53c21-7f7a-4e08-a92b-e590aa718094

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_isWt_of_eig
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_of_isWt


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
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {U : Type} [AddCommGroup U] [Module K U] (G₁ : GlW K U n) (G₂ : GlW K V n) (θ : U →ₗ[K] V)
    (hθ : ∀ c x, θ (G₁.E c c x) = G₂.E c c (θ x)) (μ : Fin n → ℤ) (x : U) :
    θ (G₁.comp μ x) = G₂.comp μ (θ x) := by
  classical
  have hwt : ∀ ν, G₂.IsWt ν (θ (G₁.comp ν x)) := fun ν => GlX.isWt_of_eig G₂ (fun c => by
    rw [← hθ, G₁.diag, map_smul])
  obtain ⟨S, hS⟩ := G₁.dec x
  have hx' := G₁.sum_comp x (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx']
  rw [map_sum, map_sum, Finset.sum_eq_single μ (fun ν _ hν => by rw [G₂.comp_of_isWt (hwt ν), if_neg (Ne.symm hν)])
    (fun h => absurd (Finset.mem_insert_self μ S) h), G₂.comp_of_isWt (hwt μ), if_pos rfl]
end Formalism.InvariantFactorPaths.PW
