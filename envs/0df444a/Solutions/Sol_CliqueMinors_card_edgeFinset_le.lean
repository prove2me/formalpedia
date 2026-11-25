-- Prove2me | solution 1 for CliqueMinors.card_edgeFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:02.59412+00:00
-- url     : https://prove2.me/submissions/30c17e49-9a21-4dc0-b373-fe0668d16be4

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_edges_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
namespace CliqueMinors
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) :
    G.edgeFinset.card + 3 ≤ 2 * Fintype.card V := by
  classical
  have := edges_aux _ G Finset.univ rfl (by rwa [Finset.card_univ])
    (fun _ _ _ => Finset.mem_univ _) h
  convert this using 3
  · ext e; simp
  · exact Finset.card_univ.symm
end CliqueMinors
