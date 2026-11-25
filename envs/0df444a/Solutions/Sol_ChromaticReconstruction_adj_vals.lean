-- Prove2me | solution 1 for ChromaticReconstruction.adj_vals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:52.079836+00:00
-- url     : https://prove2.me/submissions/90caa4b9-9a9f-4c84-aa76-85e808825de8

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
namespace ChromaticReconstruction
theorem _root_.solution {p a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) (h : s(vx n a, vx n b) ∈ (PL n p).edgeSet) :
    a + 1 = b ∨ b + 1 = a ∨ a = n ∨ b = n := by
  rw [SimpleGraph.mem_edgeSet, PL_adj_vx ha hb] at h
  omega
end ChromaticReconstruction
