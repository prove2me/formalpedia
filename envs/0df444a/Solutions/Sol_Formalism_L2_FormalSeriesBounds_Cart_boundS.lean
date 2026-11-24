-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.boundS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:15:40.417644+00:00
-- url     : https://prove2.me/submissions/2c62de93-0b75-4fdf-baf0-23d3a44fc2de

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_Vpow_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_bound0
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
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
theorem _root_.solution : ∀ (i s : ℕ) (x : ℕ → I ⊕ J → C), x ∈ X.Ty → (∀ j < s, x j = 0) →
    ∀ n, V.Ge (-(i : ℝ)) (x (s + i) n) := by
  intro i
  induction i with
  | zero =>
    intro s x hx hz n
    simpa using X.t2 x hx s hz n
  | succ i ih =>
    intro s x hx hz n
    have hint : ∀ m, V.Ge 0 (x s m) := X.t2 x hx s hz
    have hL := X.lift_mem hint
    have hx' : x - Vpow s (X.lift (x s)) ∈ X.Ty := X.Ty.sub_mem hx (X.Vpow_mem s hL)
    have hz' : ∀ j < s + 1, (x - Vpow s (X.lift (x s))) j = 0 := by
      intro j hj
      funext m
      simp only [Pi.sub_apply, Pi.zero_apply, Vpow]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
      · rw [if_pos h, hz j h]
        simp
      · subst h
        rw [if_neg (lt_irrefl _), Nat.sub_self, X.lift_zero, sub_self]
    have h1 := ih (s + 1) _ hx' hz' n
    have h2 := X.bound0 (i + 1) _ hL n
    have hsplit : x (s + (i + 1)) n =
        (x - Vpow s (X.lift (x s))) (s + 1 + i) n + X.lift (x s) (i + 1) n := by
      simp only [Pi.sub_apply, Vpow]
      rw [if_neg (by omega), show s + 1 + i - s = i + 1 by omega, show s + 1 + i = s + (i + 1) by omega]
      ring
    rw [hsplit]
    exact (h1.mono (by push_cast; linarith)).add h2
end Formalism.L2.FormalSeriesBounds.Cart
