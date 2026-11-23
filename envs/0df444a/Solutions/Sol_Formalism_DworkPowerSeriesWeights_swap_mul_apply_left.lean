-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.swap_mul_apply_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:13:55.507873+00:00
-- url     : https://prove2.me/submissions/a5dc6277-e230-45c9-b81c-2604a94332f9

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
theorem _root_.solution {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) :
    (Equiv.swap a b * τ) a = b := by
  rw [Equiv.Perm.mul_apply, hτa, Equiv.swap_apply_left]
end Formalism.DworkPowerSeriesWeights
