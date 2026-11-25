-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.rem_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:29.361616+00:00
-- url     : https://prove2.me/submissions/14c52bec-1e77-4c7f-a706-151a38511061

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C] {V : VF C} {d : ℕ} {I J : Type*}
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable [DecidableEq I]
variable [Fintype I]
namespace Formalism.L2.FormalSeriesBounds.Cart
theorem _root_.solution (x : ℕ → I ⊕ J → C) (s : ℕ) :
    X.rem x s = x - ∑ s' ∈ range s, Vpow s' (X.lift (X.rem x s' s')) := by
  induction s with
  | zero => simp [rem]
  | succ s ih =>
    show X.rem x s - Vpow s (X.lift (X.rem x s s)) = _
    rw [Finset.sum_range_succ, sub_add_eq_sub_sub, ← ih]
end Formalism.L2.FormalSeriesBounds.Cart
