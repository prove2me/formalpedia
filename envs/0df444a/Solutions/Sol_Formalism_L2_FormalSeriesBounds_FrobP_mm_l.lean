-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.FrobP.mm_l
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:33.196454+00:00
-- url     : https://prove2.me/submissions/13ba7c9f-e746-4f44-9060-00af5cbdeed1

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FrobSerSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffPowCharFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open ValuationNonnegativity
open Formalism.L2.FormalSeriesBounds.FrobP
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.FrobP
theorem _root_.solution : V.MM (V.l : C) := by
  unfold VF.MM
  rw [V.v_l]
  exact zero_lt_one
end Formalism.L2.FormalSeriesBounds.FrobP
