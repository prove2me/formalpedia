-- Prove2me | solution 1 for C6BipartiteDomination.paper11OwnerCompensation_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:12:06.562677+00:00
-- url     : https://prove2.me/submissions/97dd64ee-2d30-4d35-b099-1c7f99bf8075

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_mem_supportX
import Theorems.Thm_C6BipartiteDomination_paper11_compensation_unique_B_owner


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u v : V}
    (huB : u ∈ BPart G D) (hvB : v ∈ BPart G D) (hne : u ≠ v) :
    Disjoint (paper11OwnerCompensation G D hCan hmax u)
      (paper11OwnerCompensation G D hCan hmax v) := by
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
  exact hne (paper11_compensation_unique_B_owner G hX hY huB hvB hqU hqV)
end C6BipartiteDomination
