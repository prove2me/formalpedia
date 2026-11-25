-- Prove2me | solution 1 for ChromaticReconstruction.not_mem_of_far
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:16:49.729031+00:00
-- url     : https://prove2.me/submissions/18d4f7be-e1a9-4df2-82ee-967e05ddacad

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_adj_vals

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
namespace ChromaticReconstruction
theorem _root_.solution {a b : ℕ} (hF : F ⊆ (PL n p).edgeFinset) (ha : a ≤ n) (hb : b ≤ n)
    (h1 : a + 1 ≠ b) (h2 : b + 1 ≠ a) (h3 : a ≠ n) (h4 : b ≠ n) : s(vx n a, vx n b) ∉ F := by
  intro h
  have := adj_vals (p := p) ha hb (SimpleGraph.mem_edgeFinset.1 (hF h))
  omega
end ChromaticReconstruction
