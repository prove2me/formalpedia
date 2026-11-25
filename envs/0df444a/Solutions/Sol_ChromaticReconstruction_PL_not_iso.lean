-- Prove2me | solution 1 for ChromaticReconstruction.PL_not_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:58:54.517378+00:00
-- url     : https://prove2.me/submissions/40a199a7-a7ef-4cdb-a039-fa7250c33d1b

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_closeLeaves_of_iso
import Theorems.Thm_ChromaticReconstruction_closeLeaves_PL_pred
import Theorems.Thm_ChromaticReconstruction_not_closeLeaves_PL
import Theorems.Thm_ChromaticReconstruction_three_le_degree_PL_one
import Theorems.Thm_ChromaticReconstruction_degree_le_two_PL_zero

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n b : ℕ} (hb : 1 ≤ b) (hn : 2 * b + 1 ≤ n) :
    IsEmpty (PL n (b - 1) ≃g PL n b) := by
  refine ⟨fun e => ?_⟩
  by_cases hb2 : 2 ≤ b
  · exact not_closeLeaves_PL hb hn (closeLeaves_of_iso e (closeLeaves_PL_pred hb2 hn))
  · have hb1 : b = 1 := by omega
    subst hb1
    have := three_le_degree_PL_one (n := n) (by omega)
    have := degree_le_two_PL_zero (n := n) (e.symm (vx n 1))
    rw [SimpleGraph.Iso.degree_eq] at this
    omega
end ChromaticReconstruction
