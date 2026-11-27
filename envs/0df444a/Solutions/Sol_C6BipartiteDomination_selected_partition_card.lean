-- Prove2me | solution 1 for C6BipartiteDomination.selected_partition_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:10:38.553996+00:00
-- url     : https://prove2.me/submissions/99104b48-491d-4bee-98c4-79f9fb05e212

import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Definitions.Def_C6BipartiteDomination_MainResults
import Theorems.Thm_C6BipartiteDomination_bpart_zpart_partition
import Theorems.Thm_C6BipartiteDomination_Z0_Z1_disjoint
import Theorems.Thm_C6BipartiteDomination_ZPart_eq_Z0_union_Z1


set_option autoImplicit true
open C6BipartiteDomination
open Finset
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution (D : Finset V) :
    D.card = (BPart G D).card + (Z0Part G D).card + (Z1Part G D).card := by
  classical
  have hBZ : Disjoint (BPart G D) (ZPart G D) := by
    rw [Finset.disjoint_left]
    intro v hvB hvZ
    exact ((Finset.mem_sdiff.mp (show v ∈ D \ ZPart G D from hvB)).2) hvZ
  have hBunion := bpart_zpart_partition G D
  calc
    D.card = (BPart G D ∪ ZPart G D).card := by rw [← hBunion]
    _ = (BPart G D).card + (ZPart G D).card :=
      Finset.card_union_of_disjoint hBZ
    _ = (BPart G D).card +
        ((Z0Part G D).card + (Z1Part G D).card) := by
      rw [ZPart_eq_Z0_union_Z1 G D]
      rw [Finset.card_union_of_disjoint (Z0_Z1_disjoint G D)]
    _ = _ := by omega
end C6BipartiteDomination
