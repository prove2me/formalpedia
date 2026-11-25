-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intC_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:37.458424+00:00
-- url     : https://prove2.me/submissions/1240a621-3af7-4c2a-b8e2-2aaa5b7c9752

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv

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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution : IntC v 1 := by
  unfold IntC
  simp
end Formalism.L2.FormalSeriesBounds.AltInv
