-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.ColValS.zero_eq_succ_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:54.698816+00:00
-- url     : https://prove2.me/submissions/9503ae02-57e8-472a-b5d2-8b862d60f27b

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
theorem _root_.solution {m : ℕ} (k : Fin m) : ((0 : Fin (m+1)) = k.succ) ↔ False := iff_false_intro (fun h => Fin.succ_ne_zero k h.symm)
end Formalism.L2.GlobalTheoryTheory.ColValS
