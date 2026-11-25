-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intS_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:10.312063+00:00
-- url     : https://prove2.me/submissions/8f4dbb11-0659-4914-ab4a-43d2c1f02a82

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intS_one

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
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution {f : MvPowerSeries σ C} (hf : IntS v f) (n : ℕ) : IntS v (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact intS_one
  | succ n ih =>
    rw [pow_succ]
    exact intS_mul ih hf
end Formalism.L2.FormalSeriesBounds.AltInv
