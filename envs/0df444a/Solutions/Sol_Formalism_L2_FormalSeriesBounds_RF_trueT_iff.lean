-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.trueT_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:50.092289+00:00
-- url     : https://prove2.me/submissions/bc4ea175-d30c-4a6a-a1db-8a531d2c61b7

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IsWHLetterMinorK
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCDeg

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
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (g : Fin 2) (t' s : ZMod 2) : ((if g = 0 then t' else t' + 1) = s) ↔ t' = trueT g s := by
  unfold trueT
  revert g t' s
  decide
end Formalism.L2.FormalSeriesBounds.RF
