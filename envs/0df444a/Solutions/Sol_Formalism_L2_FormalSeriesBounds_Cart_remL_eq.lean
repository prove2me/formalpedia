-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Cart.remL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:57.785724+00:00
-- url     : https://prove2.me/submissions/27440ca8-c731-4522-8d2d-73a32b488bbb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero


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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
open Formalism.L2.FormalSeriesBounds.Cart
variable (X : Cart V d I J)
variable {X} {L : (I ⊕ J → C) → ℕ → I ⊕ J → C}
namespace Formalism.L2.FormalSeriesBounds.Cart
theorem _root_.solution (x : ℕ → I ⊕ J → C) (s : ℕ) :
    remL L x s = x - ∑ s' ∈ Finset.range s, Vpow s' (L (remL L x s' s')) := by
  induction s with
  | zero => simp [remL]
  | succ s ih =>
    show remL L x s - Vpow s (L (remL L x s s)) = _
    rw [Finset.sum_range_succ, ← sub_sub, ← ih]
end Formalism.L2.FormalSeriesBounds.Cart
