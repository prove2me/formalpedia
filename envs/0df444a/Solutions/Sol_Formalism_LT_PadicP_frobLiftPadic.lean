-- Prove2me | solution 1 for Formalism.LT.PadicP.frobLiftPadic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:30.08679+00:00
-- url     : https://prove2.me/submissions/f139301c-b4b1-42aa-bc6a-7f6f8f629b87

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_LT_PadicP_padicInt_norm_le_p

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
namespace Formalism.LT.PadicP
theorem _root_.solution : FrobLiftPadic := by
  intro p _
  refine ⟨Fact.out, ⟨1, one_pos, (pow_one p).symm⟩, Padic.norm_p_lt_one, ?_⟩
  intro a ha
  let y : ℤ_[p] := ⟨a, ha⟩
  have hy : PadicInt.toZMod (y - y ^ p) = 0 := by rw [map_sub, map_pow, ZMod.pow_card, sub_self]
  exact padicInt_norm_le_p _ hy
end Formalism.LT.PadicP
