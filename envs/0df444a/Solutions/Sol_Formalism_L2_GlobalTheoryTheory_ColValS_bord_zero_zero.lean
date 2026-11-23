-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:00.361496+00:00
-- url     : https://prove2.me/submissions/fe4f1562-1658-44bb-abc4-af712f6cada4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]
namespace Formalism.L2.GlobalTheoryTheory.ColValS
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) O) : bord M 0 0 = 1 := by
  simp [bord]
end Formalism.L2.GlobalTheoryTheory.ColValS
