-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.U_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:57:02.175824+00:00
-- url     : https://prove2.me/submissions/a41eb1ec-a19d-421c-a96c-f02ff2558a1f

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_cur_zero_inl

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
theorem _root_.solution (c k : I) : V.Ge 0 (S.U c k) := by
  have := X.t2 _ (S.mem c) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) (Sum.inl k)
  rw [S.cur_zero_inl] at this
  exact this
end Formalism.L2.FormalSeriesBounds.Sys
