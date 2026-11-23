-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.swap_mul_apply_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:17:18.184221+00:00
-- url     : https://prove2.me/submissions/ee2447c8-7fa2-451a-b8c1-53dbc9818abf

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
theorem _root_.solution {a b : Fin n} {τ : Equiv.Perm (Fin n)} (hτa : τ a = a) (hτb : τ b = b)
    {i : Fin n} (hia : i ≠ a) (hib : i ≠ b) : (Equiv.swap a b * τ) i = τ i := by
  rw [Equiv.Perm.mul_apply]
  refine Equiv.swap_apply_of_ne_of_ne (fun h => hia ?_) (fun h => hib ?_)
  · exact τ.injective (h.trans hτa.symm)
  · exact τ.injective (h.trans hτb.symm)
end Formalism.DworkPowerSeriesWeights
