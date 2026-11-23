-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.lift_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:17.537892+00:00
-- url     : https://prove2.me/submissions/c1f4daa1-656c-4bd7-89c7-c927f418ce31

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_std_spec

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
theorem _root_.solution {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) : X.lift h ∈ X.Ty := by
  unfold lift
  exact X.Ty.add_mem (X.Ty.sum_mem fun b _ => X.teich_mem _ (hh _) _ (X.std_spec b).1)
    (X.t3 _ fun j => hh _)
end Formalism.L2.FormalSeriesBounds.Cart
