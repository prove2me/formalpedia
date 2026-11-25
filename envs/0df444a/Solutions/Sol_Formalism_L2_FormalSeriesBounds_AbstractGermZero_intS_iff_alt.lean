-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AbstractGermZero.intS_iff_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:38:05.256776+00:00
-- url     : https://prove2.me/submissions/09755fc2-0de0-4baf-a7aa-7061fdfb15a6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_WipDworkInvG
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AbstractGermZeroCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.AbstractGermZero
open Formalism.IncomingBounds
variable {C : Type} [Field C] (V : VF C)
namespace Formalism.L2.FormalSeriesBounds.AbstractGermZero
theorem _root_.solution {σ : Type} (F : MvPowerSeries σ C) : IntS V F ↔ AltInv.IntS V.v F := by
  simp only [IntS, AltInv.IntS, AltInv.IntC]
  exact Iff.rfl
end Formalism.L2.FormalSeriesBounds.AbstractGermZero
