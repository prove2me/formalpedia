-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_of_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:11.069698+00:00
-- url     : https://prove2.me/submissions/958e5ffd-bde3-447f-b65a-787d38fa7431

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution {a : C} (h : V.Ge 1 a) : V.MM a := by
  unfold VF.MM
  unfold VF.Ge at h
  exact lt_of_lt_of_le (by exact_mod_cast one_pos) h
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
