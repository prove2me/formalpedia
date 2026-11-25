-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.Good.comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:30.139795+00:00
-- url     : https://prove2.me/submissions/1a1ccc91-e6c4-4b05-8fb2-73bca6e818d6

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral

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
theorem _root_.solution {ι : Type*} (s : Finset ι) {a : ZMod d} {u : ι → I → C}
    {x : ι → ℕ → I ⊕ J → C} {co : ι → C} (hco : ∀ k ∈ s, V.Ge 0 (co k))
    (h : ∀ k ∈ s, X.Good a (u k) (x k)) :
    X.Good a (∑ k ∈ s, co k • u k) (∑ k ∈ s, teich V.l (co k) (x k)) := by
  refine And.intro (And.intro ?_ (And.intro ?_ ?_)) ?_
  · exact X.Ty.sum_mem fun k hk => X.teich_mem _ (hco k hk) _ (h k hk).1.1
  · funext n
    simp only [Finset.sum_apply, teich, pow_zero, pow_one]
    calc ∑ k ∈ s, co k * x k 0 n = ∑ k ∈ s, co k * Sum.elim (u k) 0 n :=
          Finset.sum_congr rfl fun k hk => by rw [(h k hk).1.2.1]
      _ = _ := by cases n <;> simp [Finset.sum_apply]
  · intro i n hn
    simp only [Finset.sum_apply, teich]
    exact Finset.sum_eq_zero fun k hk => by rw [(h k hk).1.2.2 i n hn, mul_zero]
  · intro c
    simp only [Finset.sum_apply, teich]
    exact Finset.sum_eq_zero fun k hk => by rw [(h k hk).2 c, mul_zero]
end Good
end Formalism.L2.FormalSeriesBounds.Cart
