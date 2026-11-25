-- Prove2me | solution 1 for ChromaticReconstruction.pe_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:04.434309+00:00
-- url     : https://prove2.me/submissions/40bc0089-cbd0-4060-804a-4eb44b94c970

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_mem_edgeSet_PL


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
namespace ChromaticReconstruction
theorem _root_.solution {e : Sym2 (Fin (n + 1))} (hpn : p < n) (hF : F ⊆ (PL n p).edgeFinset)
    (he : e ∈ F) (hne : e ≠ lf n p) : ∃ i, i + 1 < n ∧ e = pe n i := by
  have := (mem_edgeSet_PL hpn _).1 (SimpleGraph.mem_edgeFinset.1 (hF he))
  rcases this with h | h
  · exact h
  · exact absurd h hne
end ChromaticReconstruction
