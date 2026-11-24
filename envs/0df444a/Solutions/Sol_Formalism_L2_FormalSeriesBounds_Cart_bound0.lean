-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.bound0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:19.870977+00:00
-- url     : https://prove2.me/submissions/4860be44-9c8b-43c5-ac91-1b84793081d5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_of_l_mul
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
namespace Formalism.L2.FormalSeriesBounds.Cart
theorem _root_.solution : ∀ (i : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → ∀ n, V.Ge (-(i : ℝ)) (x i n) := by
  intro i
  induction i with
  | zero =>
    intro x hx n
    simpa using X.t2 x hx 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) n
  | succ i ih =>
    intro x hx n
    have := (ih _ (X.F_mem x hx) n).of_l_mul
    exact this.mono (by push_cast; linarith)
end Formalism.L2.FormalSeriesBounds.Cart
