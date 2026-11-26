-- Prove2me | solution 1 for C6BipartiteDomination.paper11OwnerCompensation_subset_S
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:54.279444+00:00
-- url     : https://prove2.me/submissions/4944817a-c8e5-4035-bfc6-5a0404bfb00f

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_mem_supportX
import Theorems.Thm_C6BipartiteDomination_paper9_shared_compensation_profile


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u q : V}
    (huB : u ∈ BPart G D)
    (hq : q ∈ paper11OwnerCompensation G D hCan hmax u) :
    q ∈ SPart G D := by
  classical
  obtain ⟨w, hw, hq⟩ := Finset.mem_biUnion.mp hq
  have hwInfo := Finset.mem_filter.mp hw
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  exact (paper9_shared_compensation_profile G hX huB hq).1
end C6BipartiteDomination
