-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intC_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:33:38.781742+00:00
-- url     : https://prove2.me/submissions/6126b7b4-ce56-42df-86b5-d484cf1e1984

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_neg

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
theorem _root_.solution {x y : C} (hx : IntC v x) (hy : IntC v y) : IntC v (x - y) := by
  rw [sub_eq_add_neg]
  exact intC_add hx (intC_neg hy)
end Formalism.L2.FormalSeriesBounds.AltInv
