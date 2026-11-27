-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_compensation_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:59.351384+00:00
-- url     : https://prove2.me/submissions/4da1dbcb-22ae-4f6b-864b-1151d730a7c8

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11_compensation_unique_B_owner
import Theorems.Thm_C6BipartiteDomination_mem_supportX


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u v : V}
    (hu : u ∈ BPart G D) (hv : v ∈ BPart G D) (hne : u ≠ v) :
    Disjoint (paper11K3Compensation G D hCan hmax u)
      (paper11K3Compensation G D hCan hmax v) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqu hqv
  obtain ⟨w, hw, hqU⟩ := Finset.mem_biUnion.mp hqu
  obtain ⟨w', hw', hqV⟩ := Finset.mem_biUnion.mp hqv
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hY : supportX G D w' ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w' z).mp hz |>.1
  have huv := paper11_compensation_unique_B_owner G hX hY hu hv hqU hqV
  exact hne huv
end C6BipartiteDomination
