-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:17.329113+00:00
-- url     : https://prove2.me/submissions/19fd7c96-e2c9-44c4-b43e-c21a06bffc17

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_mm_neg

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
theorem _root_.solution {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  exact mm_add ha (mm_neg hb)
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
