-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.scaledSecond_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:26:31.557788+00:00
-- url     : https://prove2.me/submissions/f99ee00b-b677-45c8-9921-71c1c8f969d5

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
theorem _root_.solution {ι : Type*} (s : Finset ι) (x : ι → ℕ → I ⊕ J → C) (co : ι → C) (b : I) :
    X.V2 (∑ k ∈ s, teich V.l (co k) (x k)) b = ∑ k ∈ s, co k ^ (V.l ^ 2) * X.V2 (x k) b := by
  simp only [V2, Finset.sum_apply, teich, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring
end Formalism.L2.FormalSeriesBounds.Cart
