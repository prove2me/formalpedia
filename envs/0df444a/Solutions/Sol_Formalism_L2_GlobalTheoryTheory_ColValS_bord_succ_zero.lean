-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:33.264807+00:00
-- url     : https://prove2.me/submissions/c3781b06-864b-4e84-aeac-bf573536a894

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_zero
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_succ

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]
namespace Formalism.L2.GlobalTheoryTheory.ColValS
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (i : Fin m) :
    bord M i.succ 0 = 0 := by
  simp [bord]
end Formalism.L2.GlobalTheoryTheory.ColValS
