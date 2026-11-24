-- Prove2me | solution 1 for ChromaticReconstruction.edgeFinset_nonempty_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T15:19:26.271983+00:00
-- url     : https://prove2.me/submissions/283f9fc2-301a-4a66-ab20-41573ecbeda1

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]
namespace ChromaticReconstruction
theorem _root_.solution {G : SimpleGraph V} (hG : G.Connected)
    (h2 : 2 ≤ Fintype.card V) : G.edgeFinset.Nonempty := by
  rw [nonempty_iff_ne_empty]
  intro h
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card h2
  have hbot : G = ⊥ := by
    rw [← SimpleGraph.edgeSet_eq_empty, ← SimpleGraph.coe_edgeFinset, h, coe_empty]
  have := hG.preconnected u v
  rw [hbot] at this
  exact huv (SimpleGraph.reachable_bot.1 this)
end ChromaticReconstruction
