-- Prove2me | solution 1 for ChromaticReconstruction.leaf_val_PL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:02.460823+00:00
-- url     : https://prove2.me/submissions/03480c53-3129-471b-ab60-20d68530a509

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_two_le_degree_PL

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} (x : Fin (n + 1)) (hx : (PL n c).degree x ≤ 1) :
    x.val = 0 ∨ x.val + 1 = n ∨ x.val = n := by
  by_contra h
  have := two_le_degree_PL (c := c) x (by omega) (by omega)
  omega
end ChromaticReconstruction
