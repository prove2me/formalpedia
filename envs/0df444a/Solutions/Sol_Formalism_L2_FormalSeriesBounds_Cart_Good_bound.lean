-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.Good.bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:21:19.989315+00:00
-- url     : https://prove2.me/submissions/038eb0a5-f8da-48c1-9fb8-4df11fe48156

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_boundS
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_of_l_mul


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
variable {X}
namespace Formalism.L2.FormalSeriesBounds.Cart
namespace Good
theorem _root_.solution [DecidableEq I] [Fintype I] {a : ZMod d} {u : I → C} {x : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (i : ℕ) (n : I ⊕ J) : V.Ge (-((i : ℝ) + 1)) (x (i + 2) n) := by
  have hx := h.1.1
  have hF := X.F_mem _ hx
  have hζ : ∀ j, V.Ge 0 ((V.l : C) * x 1 (Sum.inr j)) := fun j => by
    have := X.t2 _ hF 0 (fun _ h => absurd h (Nat.not_lt_zero _)) (Sum.inr j)
    exact this
  have hw : Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) ∈ X.Ty :=
    X.Ty.sub_mem hF (X.t3 _ hζ)
  have hw0 : ∀ j < 1, (Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) :
      ℕ → I ⊕ J → C) j = 0 := by
    intro j hj
    obtain rfl : j = 0 := by omega
    funext m
    cases m with
    | inl c => simp [Fs, const0, h.2 c]
    | inr k => simp [Fs, const0]
  have hb := X.boundS i 1 _ hw hw0 n
  have he : (Fs V.l x - const0 (Sum.elim 0 (fun j => (V.l : C) * x 1 (Sum.inr j))) :
      ℕ → I ⊕ J → C) (1 + i) n =
      (V.l : C) * x (i + 2) n := by
    simp only [Pi.sub_apply, Fs, const0]
    rw [if_neg (by omega), sub_zero, show 1 + i + 1 = i + 2 by omega]
  rw [he] at hb
  exact hb.of_l_mul.mono (by linarith)
end Good
end Formalism.L2.FormalSeriesBounds.Cart
