-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.GmExArith.mm_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:11:38.624642+00:00
-- url     : https://prove2.me/submissions/03bf8844-43a7-4a5e-be79-3e4a20d66103

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
theorem _root_.solution {ε : ℝ} (hε : 0 < ε) {a : C} (h : V.Ge ε a) : V.MM a :=
  lt_of_lt_of_le (by exact_mod_cast hε) h
end Formalism.L2.FormalSeriesBounds.GmExArith
