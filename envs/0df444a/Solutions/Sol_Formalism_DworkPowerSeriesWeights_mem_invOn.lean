-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.mem_invOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:26.952915+00:00
-- url     : https://prove2.me/submissions/95fd9ddd-b3da-4042-a32f-a8d7229ceb30

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffQuadSer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
variable {n : ℕ}
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {s : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ invOn s ↔ σ * σ = 1 ∧ ∀ i, i ∉ s → σ i = i := by
  simp [invOn]
end Formalism.DworkPowerSeriesWeights
