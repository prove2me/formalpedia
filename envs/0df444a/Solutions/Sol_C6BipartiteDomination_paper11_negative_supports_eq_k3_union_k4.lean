-- Prove2me | solution 1 for C6BipartiteDomination.paper11_negative_supports_eq_k3_union_k4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:43.981405+00:00
-- url     : https://prove2.me/submissions/2805cd7f-3526-4c6f-81bb-ded6fe08bd2e

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification


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
    paper11NegativeSupports G D =
      paper11K3Supports G D ∪ paper11K4Supports G D := by
  classical
  ext w
  constructor
  · intro hw
    have hi := Finset.mem_filter.mp hw
    rcases lemma_7_2_negative_charge_classification G hCan hmax hi.1 hi.2 with
      h3 | h3 | h4
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h3.1⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, h3.1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, h4.1⟩)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact (Finset.mem_filter.mp hw).1
    · exact (Finset.mem_filter.mp hw).1
end C6BipartiteDomination
