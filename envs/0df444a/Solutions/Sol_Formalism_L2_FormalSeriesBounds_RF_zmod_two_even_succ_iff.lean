-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.zmod_two_even_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:17:31.395531+00:00
-- url     : https://prove2.me/submissions/d411aafa-d9b9-4310-91f9-309351c02092

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm

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
open Formalism.IncomingBounds
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (a : ZMod 2) : Even (a + 1).val ↔ ¬ Even a.val := by revert a; decide
end Formalism.L2.FormalSeriesBounds.RF
