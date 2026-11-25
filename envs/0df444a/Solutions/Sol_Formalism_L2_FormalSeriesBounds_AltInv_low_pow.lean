-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.low_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:48.693206+00:00
-- url     : https://prove2.me/submissions/7cfe8400-1a39-4c34-bf9e-1a241c69ead6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_low_one

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
theorem _root_.solution {E D : ℕ} {f : MvPowerSeries σ C} (hf : OrdV D f) (hf' : LowLt (v := v) (E + D) f) (n : ℕ) :
    OrdV (n * D) (f ^ n) ∧ LowLt (v := v) (E + n * D) (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, Nat.zero_mul, Nat.add_zero]
    exact low_one E
  | succ n ih =>
    rw [pow_succ, Nat.add_mul, Nat.one_mul]
    exact low_mul ih.1 ih.2 hf hf'
end Formalism.L2.FormalSeriesBounds.AltInv
