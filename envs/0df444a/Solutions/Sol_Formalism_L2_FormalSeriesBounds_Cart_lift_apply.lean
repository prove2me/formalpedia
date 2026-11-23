-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.lift_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:39:15.96984+00:00
-- url     : https://prove2.me/submissions/7afeb8a6-2839-40aa-9c02-3e095c615c79

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
variable [DecidableEq I]
variable [Fintype I]
namespace Formalism.L2.FormalSeriesBounds.Cart
theorem _root_.solution (h : I ⊕ J → C) (i : ℕ) (n : I ⊕ J) : X.lift h i n =
    (∑ b, h (Sum.inl b) ^ (V.l ^ i) * X.std b i n) +
      const0 (Sum.elim 0 (fun j => h (Sum.inr j))) i n := by
  simp only [lift, Pi.add_apply, Finset.sum_apply, teich]
end Formalism.L2.FormalSeriesBounds.Cart
