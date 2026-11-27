-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.mm_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:23:24.340249+00:00
-- url     : https://prove2.me/submissions/c7888640-0bc9-4645-9b26-589a3f6e4c3e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.GmExArith
theorem _root_.solution {a : C} (h : V.MM a) : V.Ge 0 a := by
  unfold VF.Ge; rw [WithTop.coe_zero]; exact le_of_lt h
end Formalism.L2.FormalSeriesBounds.GmExArith
