-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.mm_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:39.90955+00:00
-- url     : https://prove2.me/submissions/fb78213a-6b66-4f7e-af30-b2ad42209f71

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_iff

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
theorem _root_.solution {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  have h0 := valuation_nonneg_iff.mp ha
  unfold VF.MM at *
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left h0)
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
