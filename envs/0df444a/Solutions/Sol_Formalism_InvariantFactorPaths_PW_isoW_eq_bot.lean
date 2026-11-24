-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.isoW_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:50:26.278084+00:00
-- url     : https://prove2.me/submissions/6d01aacb-8df8-4da2-9fb3-e2bca385ec33

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_PolLeISupIsoW

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G : GlW K V n) (W : Submodule K V) {S : Finset (Fin n → ℤ)}
    (hS : ∀ x ∈ W, ∀ μ ∉ S, G.comp μ x = 0) {μ : Fin n → ℤ} (hμ : μ ∉ S) : IsoW G W μ = ⊥ := by
  refine eq_bot_iff.mpr (sInf_le ⟨?_, ?_⟩)
  · rintro v ⟨hv, hvW⟩
    have h1 : G.comp μ v = v := hv.1
    rw [SetLike.mem_coe, Submodule.mem_bot, ← h1]
    exact hS v hvW μ hμ
  · intro a b x hx
    rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]
end Formalism.InvariantFactorPaths.PW
