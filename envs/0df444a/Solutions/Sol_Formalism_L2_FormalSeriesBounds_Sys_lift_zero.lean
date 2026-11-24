-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.lift_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:17:52.276176+00:00
-- url     : https://prove2.me/submissions/6c4076bb-ad04-4710-a4a8-b559ef9bb297

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_cur_zero_inl
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_be_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_co_spec
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_lift_apply
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Cart_lift_apply


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
open Formalism.L2.FormalSeriesBounds.Sys
variable {X : Cart V d I J} (S : Sys X)
namespace Formalism.L2.FormalSeriesBounds.Sys
theorem _root_.solution (h : I ⊕ J → C) : S.lift h 0 = h := by
  funext n
  rw [lift_apply]
  rcases n with k | κ
  · simp only [pow_zero, pow_one, cur_zero_inl, const0, if_true, Sum.elim_inl, Pi.zero_apply, add_zero]
    exact S.co_spec h k
  · simp only [pow_zero, pow_one, be_zero, mul_zero, Finset.sum_const_zero, const0, if_true,
      Sum.elim_inr, zero_add]
end Formalism.L2.FormalSeriesBounds.Sys
