-- Prove2me | solution 1 for ChromaticReconstruction.degree_le_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:02:38.83883+00:00
-- url     : https://prove2.me/submissions/a967d2b9-0b9f-4f23-9a92-47e11e23a2c9

import Definitions.Def_RequestProject_PathLeafSwap
import Definitions.Def_RequestProject_CountingLower
import Definitions.Def_RequestProject_TauBound

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {V : Type*} [Fintype V] {G : SimpleGraph V} {x : V} (S : Finset V)
    (hx : ∀ y, G.Adj x y → y ∈ S) : G.degree x ≤ S.card := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  exact card_le_card fun y hy => hx y ((SimpleGraph.mem_neighborFinset _ _ _).1 hy)
end ChromaticReconstruction
