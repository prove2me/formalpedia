-- Prove2me | solution 1 for C6BipartiteDomination.support_union_card_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:14.323805+00:00
-- url     : https://prove2.me/submissions/ebb70667-2e86-4256-9131-f11155c8191b

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_mem_supportX
import Theorems.Thm_C6BipartiteDomination_supportX_card
import Theorems.Thm_C6BipartiteDomination_supportB_card
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} {w : V} :
    kCharge G D w + betaCharge G D w ≤ degreeTo G Finset.univ w := by
  classical
  have hdisj : Disjoint (supportX G D w) (supportB G D w) := by
    rw [Finset.disjoint_left]
    intro z hzX hzB
    have hsep := Finset.disjoint_left.mp (Z0_disjoint_B G (D := D))
    exact hsep ((mem_supportX G D w z).mp hzX |>.1)
      ((Finset.mem_filter.mp hzB).1)
  have hsub : supportX G D w ∪ supportB G D w ⊆
      Finset.univ.filter (fun z => G.Adj w z) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzB
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (mem_supportX G D w z).mp hzX |>.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hzB).2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, supportX_card, supportB_card] at hcard
  simpa [degreeTo] using hcard
end C6BipartiteDomination
