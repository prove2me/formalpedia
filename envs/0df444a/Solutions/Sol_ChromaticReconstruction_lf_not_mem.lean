-- Prove2me | solution 1 for ChromaticReconstruction.lf_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:58.472522+00:00
-- url     : https://prove2.me/submissions/a1b9e911-3a80-4a96-b2d6-39f81d5900b7

import Definitions.Def_RequestProject_PathLeaf
import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_PathLeafSwap
import Theorems.Thm_ChromaticReconstruction_lf_inj
import Theorems.Thm_ChromaticReconstruction_mem_edgeSet_PL
import Theorems.Thm_ChromaticReconstruction_pe_ne_lf


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {n c : ℕ}
variable {p : ℕ} {F : Finset (Sym2 (Fin (n + 1)))}
namespace ChromaticReconstruction
theorem _root_.solution {q : ℕ} (hpn : p < n) (hqn : q < n) (hpq : p ≠ q)
    (hF : F ⊆ (PL n p).edgeFinset) : lf n q ∉ F := by
  intro h
  have := (mem_edgeSet_PL hpn _).1 (SimpleGraph.mem_edgeFinset.1 (hF h))
  rcases this with ⟨i, hi, h'⟩ | h'
  · exact pe_ne_lf hi hqn.le h'.symm
  · exact hpq ((lf_inj hqn hpn).1 h').symm
end ChromaticReconstruction
