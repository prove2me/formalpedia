-- Prove2me | solution 1 for C6BipartiteDomination.paper9_repair_degree_eq_one_at_k4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:10.003864+00:00
-- url     : https://prove2.me/submissions/450e105f-6bf4-4c67-be87-a5a1fccf418c

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paper9_repair_degree_le_one_at_k4

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
    {u w₄ : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w)
    (hw₄ : w₄ ∈ T) (hk₄ : kCharge G D w₄ = 4) :
    T.card = 1 := by
  have hle := paper9_repair_degree_le_one_at_k4 G hCan hmax huB T
    hTsub hTnegative hTrepair hw₄ hk₄
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨w₄, hw₄⟩
  omega
end C6BipartiteDomination
