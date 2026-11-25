-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.minorMonomial_mem_ZP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:15:54.058673+00:00
-- url     : https://prove2.me/submissions/29fb9f6f-a865-4cfa-b69e-a659f3b58d52

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_minorK_mem_ZP

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (N N' : ℕ) (e : ℕ → ℕ) : monP C N N' e ∈ ZP C (Fin N × Fin N') := by
  unfold monP
  exact prod_mem fun k _ => pow_mem (minorK_mem_ZP N N' k) _
end Formalism.L2.FormalSeriesBounds.RF
