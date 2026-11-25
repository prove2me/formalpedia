-- Prove2me | solution 1 for ChromaticReconstruction.PL_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:52.919897+00:00
-- url     : https://prove2.me/submissions/45560acc-ca0e-411b-8b58-aaa0101d5853

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf
import Theorems.Thm_ChromaticReconstruction_vx_eq_self
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx
import Theorems.Thm_ChromaticReconstruction_card_edgeFinset_PL

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} (hc : c < n) : (PL n c).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · have hpath : ∀ i, i < n → (PL n c).Reachable (vx n 0) (vx n i) := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        refine (ih (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        rw [PL_adj_vx (by omega) (by omega)]
        omega
    have hall : ∀ x : Fin (n + 1), (PL n c).Reachable (vx n 0) x := by
      intro x
      rw [← vx_eq_self x]
      by_cases hx : x.val < n
      · exact hpath _ hx
      · have : x.val = n := by omega
        rw [this]
        refine (hpath c hc).trans (SimpleGraph.Adj.reachable ?_)
        rw [PL_adj_vx (by omega) le_rfl]
        omega
    haveI : Nonempty (Fin (n + 1)) := ⟨0⟩
    exact ⟨fun u v => (hall u).symm.trans (hall v)⟩
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, card_edgeFinset_PL hc,
      Nat.card_eq_fintype_card, Fintype.card_fin]
end ChromaticReconstruction
