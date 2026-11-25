-- Prove2me | solution 1 for ChromaticReconstruction.PL_walk_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:18:07.427796+00:00
-- url     : https://prove2.me/submissions/4cfc3663-1e4e-4f4e-8963-3f89c6605cd0

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound
import Theorems.Thm_ChromaticReconstruction_PL_adj_vx


set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {n c : ℕ} : ∀ i, i < n → ∃ w : (PL n c).Walk (vx n 0) (vx n i), w.length = i
  | 0, _ => ⟨SimpleGraph.Walk.nil, rfl⟩
  | i + 1, hi => by
    obtain ⟨w, hw⟩ := solution (n := n) (c := c) i (by omega)
    have hadj : (PL n c).Adj (vx n i) (vx n (i + 1)) := by
      rw [PL_adj_vx (by omega) (by omega)]; omega
    exact ⟨w.concat hadj, by rw [SimpleGraph.Walk.length_concat, hw]⟩
end ChromaticReconstruction
