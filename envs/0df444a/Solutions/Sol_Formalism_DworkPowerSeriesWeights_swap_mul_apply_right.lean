-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.swap_mul_apply_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:51.247048+00:00
-- url     : https://prove2.me/submissions/9ecc479a-ef15-4ba0-ae4b-7a60dc608938

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
theorem _root_.solution {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτb : τ b = b) :
    (Equiv.swap a b * τ) b = a := by
  rw [Equiv.Perm.mul_apply, hτb, Equiv.swap_apply_right]
end Formalism.DworkPowerSeriesWeights
