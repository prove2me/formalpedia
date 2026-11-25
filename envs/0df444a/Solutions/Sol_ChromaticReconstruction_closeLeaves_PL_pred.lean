-- Prove2me | solution 1 for ChromaticReconstruction.closeLeaves_PL_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:35.165742+00:00
-- url     : https://prove2.me/submissions/26a683f7-eb34-4216-ba57-6b95864a91ee

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_PL_walk_zero
import Theorems.Thm_ChromaticReconstruction_degree_le_of_adj
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx
import Theorems.Thm_ChromaticReconstruction_vx_eq_self
import Theorems.Thm_ChromaticReconstruction_vx_inj


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n b : ℕ} (hb : 2 ≤ b) (hn : 2 * b + 1 ≤ n) :
    CloseLeaves (PL n (b - 1)) b := by
  obtain ⟨w, hw⟩ := PL_walk_zero (c := b - 1) (n := n) (b - 1) (by omega)
  have hadj : (PL n (b - 1)).Adj (vx n (b - 1)) (vx n n) := by
    rw [PL_adj_vx (by omega) le_rfl]; omega
  refine ⟨vx n 0, vx n n, by rw [Ne, vx_inj (by omega) le_rfl]; omega, ?_, ?_,
    w.concat hadj, by rw [SimpleGraph.Walk.length_concat]; omega⟩
  · refine (degree_le_of_adj {vx n 1} fun y hy => ?_).trans (card_singleton _).le
    rw [← vx_eq_self y, PL_adj_vx (by omega) (by omega)] at hy
    rw [mem_singleton, ← vx_eq_self y, vx_inj (by omega) (by omega)]
    omega
  · refine (degree_le_of_adj {vx n (b - 1)} fun y hy => ?_).trans (card_singleton _).le
    rw [← vx_eq_self y, PL_adj_vx (by omega) (by omega)] at hy
    rw [mem_singleton, ← vx_eq_self y, vx_inj (by omega) (by omega)]
    omega
end ChromaticReconstruction
