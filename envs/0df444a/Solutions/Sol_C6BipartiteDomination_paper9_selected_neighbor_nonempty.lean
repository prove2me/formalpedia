-- Prove2me | solution 1 for C6BipartiteDomination.paper9_selected_neighbor_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:27.677802+00:00
-- url     : https://prove2.me/submissions/78ee08f4-6590-45f6-93ec-0945c8b21f30

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_nonisolated_of_mem_BPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {u : V} (hCan : CanonicalTwoLevelOptimum G D)
    (huB : u ∈ BPart G D) :
    0 < (D.filter fun q => G.Adj u q).card := by
  classical
  obtain ⟨v, hvD, huv⟩ := (nonisolated_of_mem_BPart G huB).2
  apply Finset.card_pos.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨hvD, huv⟩⟩
end C6BipartiteDomination
