-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.Good.wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:40:03.928709+00:00
-- url     : https://prove2.me/submissions/9cf18d3e-84fe-44f0-8f12-bb658ea878f2

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
theorem _root_.solution {a : ZMod d} {u : I → C} {x x' : ℕ → I ⊕ J → C}
    (h : X.Good a u x) (h' : X.Good a u x') (n : I ⊕ J) : V.Ge 0 (x 2 n - x' 2 n) := by
  have hz : x - x' ∈ X.Ty := X.Ty.sub_mem h.1.1 h'.1.1
  have hz0 : (x - x') 0 = 0 := by rw [Pi.sub_apply, h.1.2.1, h'.1.2.1, sub_self]
  have hγ : ∀ j, V.Ge 0 (x 1 (Sum.inr j) - x' 1 (Sum.inr j)) := fun j => by
    have := X.t2 _ hz 1 (fun i hi => by rw [show i = 0 by omega]; exact hz0) (Sum.inr j)
    simpa using this
  have hw : (x - x') - Vpow 1 (const0 (Sum.elim 0 (fun j => x 1 (Sum.inr j) - x' 1 (Sum.inr j)))) ∈ X.Ty :=
    X.Ty.sub_mem hz (X.V_mem _ (X.t3 _ hγ))
  have hw0 : ∀ i < 2, ((x - x') - Vpow 1 (const0 (Sum.elim 0
      (fun j => x 1 (Sum.inr j) - x' 1 (Sum.inr j)))) : ℕ → I ⊕ J → C) i = 0 := by
    intro i hi
    funext m
    interval_cases i
    · simp [Vpow, h.1.2.1, h'.1.2.1]
    · cases m with
      | inl c => simp [Vpow, const0, h.2 c, h'.2 c]
      | inr j => simp [Vpow, const0]
  have hw2 := X.t2 _ hw 2 hw0 n
  simpa [Vpow, const0] using hw2
end Good
end Formalism.L2.FormalSeriesBounds.Cart
