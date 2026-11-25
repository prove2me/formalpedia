-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intC_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:19.222353+00:00
-- url     : https://prove2.me/submissions/6d1083cd-b2fa-48c6-86cd-26f057fa6bf9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_one
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_add

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
theorem _root_.solution (n : ℕ) : IntC v (n : C) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact intC_zero
  | succ n ih =>
    rw [Nat.cast_succ]
    exact intC_add ih intC_one
end Formalism.L2.FormalSeriesBounds.AltInv
