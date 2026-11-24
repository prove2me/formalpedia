-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.two_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:56:55.350801+00:00
-- url     : https://prove2.me/submissions/273febb1-7555-44c5-b00d-f5afca47f8ac

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {X : Cart V d I J}
open Formalism.L2.FormalSeriesBounds.Sys
variable (S : Sys X)
namespace Formalism.L2.FormalSeriesBounds.Sys
theorem _root_.solution (s : ℕ) : 2 ≤ V.l ^ (s + 1) := by
  first
  | exact V.3.two_le.trans (Nat.le_self_pow (Nat.succ_ne_zero s) _)
  | exact le_trans V.3.two_le (Nat.le_self_pow (by omega) _)
  | calc 2 ≤ V.l := V.3.two_le
      _ = V.l ^ 1 := (pow_one _).symm
      _ ≤ V.l ^ (s + 1) := Nat.pow_le_pow_right V.3.pos (by omega)
end Formalism.L2.FormalSeriesBounds.Sys
