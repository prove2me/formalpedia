-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.ColValS.rowS_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:14.038025+00:00
-- url     : https://prove2.me/submissions/974bad8a-a9f3-496f-8e7f-5998f0fc75c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ElemZeroZeroMulApply
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_zero_succ
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_succ_zero
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_bord_succ_succ
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_zero_eq_succ_iff
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_ColValS_colS_apply
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
attribute [local simp] Formalism.L2.GlobalTheoryTheory.ColValS.colS_apply

set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.ColValS
open Matrix
variable {O : Type} [CommRing O]
namespace Formalism.L2.GlobalTheoryTheory.ColValS
theorem _root_.solution {m : ℕ} (g : Fin m → O) (i j : Fin (m+1)) :
    rowS g i j = (1 : Matrix (Fin (m+1)) (Fin (m+1)) O) i j +
      Fin.cases 0 (fun k => if i = 0 then g k else 0) j := by
  simp only [rowS, Matrix.add_apply, Matrix.sum_apply, Matrix.single_apply]
  congr 1
  induction j using Fin.cases with
  | zero => simp
  | succ j => by_cases hi : i = 0 <;> simp [hi, eq_comm]
end Formalism.L2.GlobalTheoryTheory.ColValS
