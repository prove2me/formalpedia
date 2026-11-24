-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Vpow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:57:00.749644+00:00
-- url     : https://prove2.me/submissions/cccbccc3-a4c0-419e-8dff-a9539ef80b0f

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
variable {N : Type*}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (s : ℕ) (x : ℕ → N → C) : Vpow (s + 1) x = Vpow 1 (Vpow s x) := by
  funext i n
  simp only [Vpow]
  split_ifs <;> first | rfl | omega | (congr 1; omega)
end Formalism.L2.FormalSeriesBounds
