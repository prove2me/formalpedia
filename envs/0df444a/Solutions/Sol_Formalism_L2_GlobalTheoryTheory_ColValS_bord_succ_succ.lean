-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:29:57.057786+00:00
-- url     : https://prove2.me/submissions/6a941f2f-1771-4af0-849e-6feededc00d3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_succ
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_succ_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_zero
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.bord_zero_succ
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_zero

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]
namespace Formalism.L2.GlobalTheoryTheory.ColValS
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) O) (i j : Fin m) :
    bord M i.succ j.succ = M i j := by
  simp [bord]
end Formalism.L2.GlobalTheoryTheory.ColValS
