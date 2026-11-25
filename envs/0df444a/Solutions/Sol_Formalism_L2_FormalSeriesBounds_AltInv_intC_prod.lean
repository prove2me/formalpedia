-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intC_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:20.154843+00:00
-- url     : https://prove2.me/submissions/d8c4d067-a162-4235-9ef4-8cf7c26b58df

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_mul

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {f : ι → C} (h : ∀ i ∈ s, IntC v (f i)) :
    IntC v (∏ i ∈ s, f i) :=
  Finset.prod_induction _ (IntC v) (fun _ _ => intC_mul) intC_one h
end Formalism.L2.FormalSeriesBounds.AltInv
