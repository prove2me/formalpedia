-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.lift_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:14:42.395523+00:00
-- url     : https://prove2.me/submissions/f6d00fbd-0b47-44e0-8a19-8bbe3e09b1fc

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_co_int

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
theorem _root_.solution {h : I ⊕ J → C} (hh : ∀ n, V.Ge 0 (h n)) : S.lift h ∈ X.Ty := add_mem (sum_mem fun b _ => X.teich_mem _ (S.co_int hh b) _ (S.mem b)) (X.t3 _ fun j => hh _)
end Formalism.L2.FormalSeriesBounds.Sys
