-- Prove2me | solution 1 for ChromaticReconstruction.two_le_degree_PL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:20:37.463183+00:00
-- url     : https://prove2.me/submissions/a45e0d45-fafd-4165-873c-77e8620d1b7b

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx
import Theorems.Thm_ChromaticReconstruction_vx_eq_self
import Theorems.Thm_ChromaticReconstruction_vx_inj


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} (x : Fin (n + 1)) (h1 : 1 ≤ x.val) (h2 : x.val + 1 < n) :
    2 ≤ (PL n c).degree x := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : ({vx n (x.val - 1), vx n (x.val + 1)} : Finset _) ⊆ (PL n c).neighborFinset x := by
    intro y hy
    rw [mem_insert, mem_singleton] at hy
    rw [SimpleGraph.mem_neighborFinset, ← vx_eq_self x]
    rcases hy with rfl | rfl
    · rw [PL_adj_vx (by omega) (by omega)]; omega
    · rw [PL_adj_vx (by omega) (by omega)]; omega
  have hne : vx n (x.val - 1) ≠ vx n (x.val + 1) := by
    rw [Ne, vx_inj (by omega) (by omega)]; omega
  have := card_le_card hsub
  rw [card_pair hne] at this
  exact this
end ChromaticReconstruction
