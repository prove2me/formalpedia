-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intC_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:40:58.975162+00:00
-- url     : https://prove2.me/submissions/d6b65eba-0a10-4f12-bf8e-585937f80731

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_natCast

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
theorem _root_.solution (n : ℤ) : IntC v (n : C) := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact intC_natCast n
  | negSucc n =>
    rw [Int.cast_negSucc]
    exact intC_neg (intC_natCast _)
end Formalism.L2.FormalSeriesBounds.AltInv
