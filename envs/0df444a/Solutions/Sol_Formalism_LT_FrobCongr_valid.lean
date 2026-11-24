-- Prove2me | solution 1 for Formalism.LT.FrobCongr_valid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:56.695797+00:00
-- url     : https://prove2.me/submissions/34831f5f-57fb-405e-b22a-e31e870424b1

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Theorems.Thm_Formalism_LT_FrobP_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT
open Formalism.G
namespace Formalism.LT
theorem _root_.solution : Formalism.LT.FrobCongr.{u, v} := by
  intro K _ _ _ p q hq σ hset ι A hA
  obtain ⟨hpr, ⟨h, _, rfl⟩, hp, hσ⟩ := hset
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  exact FrobP.main p h hpr σ hp0 hp hσ A hA
end Formalism.LT
