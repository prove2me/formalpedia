-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:12.281288+00:00
-- url     : https://prove2.me/submissions/3224ddd1-4c09-4e46-8ed6-cf4f225601a7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_zero

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]
namespace Formalism.L2.GlobalTheoryTheory.ColValS
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (j : Fin m) :
    bord M 0 j.succ = 0 := by
  simp [bord]
end Formalism.L2.GlobalTheoryTheory.ColValS
