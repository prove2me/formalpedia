-- Prove2me | solution 1 for C6BipartiteDomination.paper9_sCharge_add_xCharge_le_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:26.459653+00:00
-- url     : https://prove2.me/submissions/6dd5d18e-803b-4e8f-adcb-50c0f30834ea

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paper9_neighbor_partition
import Theorems.Thm_C6BipartiteDomination_paper9_neighbor_partition_disjoint
import Theorems.Thm_C6BipartiteDomination_paper9_selected_neighbor_nonempty
import Theorems.Thm_C6BipartiteDomination_private_card_eq_two_add_x


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) :
    sCharge G D u + xCharge G D u ≤ 3 := by
  classical
  have hpart := paper9_neighbor_partition G hCan huB
  have hdisj := paper9_neighbor_partition_disjoint G huB
  have hcard := congrArg Finset.card hpart
  rw [Finset.card_union_of_disjoint hdisj.1,
    Finset.card_union_of_disjoint hdisj.2] at hcard
  have hdeg : (Finset.univ.filter fun q => G.Adj u q).card =
      degreeTo G Finset.univ u := by
    simp [degreeTo, G.adj_comm]
  have hSle : ((SPart G D).filter fun q => G.Adj u q).card =
      degreeTo G (SPart G D) u := by
    simp [degreeTo, G.adj_comm]
  rw [hdeg, hSle, private_card_eq_two_add_x G hCan huB] at hcard
  have hselected := paper9_selected_neighbor_nonempty G hCan huB
  have hmaxu := hmax u
  change degreeTo G (SPart G D) u + xCharge G D u ≤ 3
  omega
end C6BipartiteDomination
