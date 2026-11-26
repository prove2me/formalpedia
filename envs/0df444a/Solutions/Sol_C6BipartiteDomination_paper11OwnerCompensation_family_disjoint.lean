-- Prove2me | solution 1 for C6BipartiteDomination.paper11OwnerCompensation_family_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:05.715346+00:00
-- url     : https://prove2.me/submissions/d63678ac-dc87-4c66-b602-2c653e5b7f31

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11AllRepairOwners_subset_B
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
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (paper11AllRepairOwners G D hCan hmax : Set V).PairwiseDisjoint
      (paper11OwnerCompensation G D hCan hmax) := by
  classical
  rw [Finset.pairwiseDisjoint_iff]
  intro u hu v hv hne
  have huB := paper11AllRepairOwners_subset_B G hCan hmax hu
  have hvB := paper11AllRepairOwners_subset_B G hCan hmax hv
  rcases hne with ⟨q, hq⟩
  have hqBoth := Finset.mem_inter.mp hq
  obtain ⟨w, hw, hqU⟩ := Finset.mem_biUnion.mp hqBoth.1
  obtain ⟨w', hw', hqV⟩ := Finset.mem_biUnion.mp hqBoth.2
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hY : supportX G D w' ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w' z).mp hz |>.1
  exact paper11_compensation_unique_B_owner G hX hY huB hvB hqU hqV
end C6BipartiteDomination
