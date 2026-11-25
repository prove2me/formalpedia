-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intC_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:04.733577+00:00
-- url     : https://prove2.me/submissions/7c702511-1e6a-4e58-a440-dd5ea9e61c89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sum

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
theorem _root_.solution {ι : Type*} {f : ι → C} (h : ∀ i, IntC v (f i)) : IntC v (∑ᶠ i, f i) := by
  by_cases hs : (Function.support f).Finite
  · rw [finsum_eq_sum f hs]
    exact intC_sum _ fun i _ => h i
  · rw [finsum_of_infinite_support hs]
    exact intC_zero
end Formalism.L2.FormalSeriesBounds.AltInv
