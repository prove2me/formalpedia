-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.trueT_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:20:51.26286+00:00
-- url     : https://prove2.me/submissions/f78a532b-21b8-4ece-ad35-6ed1b64ab77e

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
theorem _root_.solution : ∀ t : ZMod 2, trueT 1 (t + 1) = t := by
  unfold trueT
  decide
end Formalism.L2.FormalSeriesBounds.RF
