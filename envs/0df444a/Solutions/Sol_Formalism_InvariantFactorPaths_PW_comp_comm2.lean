-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.comp_comm2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:27:16.958486+00:00
-- url     : https://prove2.me/submissions/dcc7da3c-9cff-4b16-a3b3-c46307780f06

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_CountingSumsFrames_GlX_isWt_of_eig


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
theorem _root_.solution (G₁ : GlW K U n) (G₂ : GlW K V n) (θ : U →ₗ[K] V)
    (hθ : ∀ c x, θ (G₁.E c c x) = G₂.E c c (θ x)) (μ : Fin n → ℤ) (x : U) :
    θ (G₁.comp μ x) = G₂.comp μ (θ x) := by
  have hw : ∀ ν, G₂.comp ν (θ (G₁.comp ν x)) = θ (G₁.comp ν x) := fun ν =>
    GlX.isWt_of_eig (G := G₂) (fun c => by rw [← hθ, G₁.diag, map_smul])
  obtain ⟨S, hS⟩ := G₁.dec x
  have hx : ∑ ν ∈ insert μ S, G₁.comp ν x = x :=
    G₁.sum_comp x _ (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx]
  rw [map_sum, map_sum, Finset.sum_eq_single μ]
  · exact (hw μ).symm
  · intro ν _ hne
    rw [← hw ν, G₂.idem, if_neg (Ne.symm hne)]
  · intro h
    exact absurd (Finset.mem_insert_self μ S) h
end Formalism.InvariantFactorPaths.PW
