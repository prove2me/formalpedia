-- Prove2me | solution 1 for C6BipartiteDomination.paper11_nonnegative_charge_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:26.397846+00:00
-- url     : https://prove2.me/submissions/0d5d7bde-9b75-46f7-a1d8-d96521b54623

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    SPart G D = paper11NegativeSupports G D ∪
      paper11NonnegativeSupports G D := by
  classical
  ext w
  constructor
  · intro hw
    by_cases hneg : externalCharge G D w < 0
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hneg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨hw, by
          intro hN
          exact hneg (Finset.mem_filter.mp hN).2⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_filter.mp hw).1
    · exact (Finset.mem_sdiff.mp hw).1
end C6BipartiteDomination
