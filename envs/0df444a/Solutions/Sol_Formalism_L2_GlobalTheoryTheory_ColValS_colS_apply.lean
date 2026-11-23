-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.ColValS.colS_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:19.886266+00:00
-- url     : https://prove2.me/submissions/d852ceb3-8059-4864-8894-53829f2b5081

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_succ
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_succ_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_succ_succ
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_zero_eq_succ_iff
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
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.bord_succ_succ
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.zero_eq_succ_iff

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]
namespace Formalism.L2.GlobalTheoryTheory.ColValS
theorem _root_.solution {m : ℕ} (f : Fin m → O) (i j : Fin (m+1)) :
    colS f i j = (1 : Matrix (Fin (m+1)) (Fin (m+1)) O) i j +
      Fin.cases 0 (fun k => if j = 0 then f k else 0) i := by
  simp only [colS, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply]
  congr 1
  induction i using Fin.cases with
  | zero => simp
  | succ i => by_cases hj : j = 0 <;> simp [hj, eq_comm]
end Formalism.L2.GlobalTheoryTheory.ColValS
