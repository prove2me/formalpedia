-- Prove2me | solution 1 for C6BipartiteDomination.paper11_base_charge_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:19.809613+00:00
-- url     : https://prove2.me/submissions/3a30a99f-a276-43c7-b1b0-3f4d7e6e8875

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11AllRepairOwners_subset_B
import Theorems.Thm_C6BipartiteDomination_paper11_charge_nonnegative_on_B

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
    (∑ u ∈ paper11AllRepairOwners G D hCan hmax, vertexCharge G D u) ≤
      ∑ u ∈ BPart G D, vertexCharge G D u := by
  classical
  let O := paper11AllRepairOwners G D hCan hmax
  let B := BPart G D
  have hsub : O ⊆ B := by simpa [O, B] using
    paper11AllRepairOwners_subset_B G hCan hmax
  have hdecomp : B = O ∪ (B \ O) := by
    ext u
    constructor
    · intro huB
      by_cases huO : u ∈ O
      · exact Finset.mem_union_left _ huO
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨huB, huO⟩)
    · intro hu
      rcases Finset.mem_union.mp hu with huO | huBO
      · exact hsub huO
      · exact (Finset.mem_sdiff.mp huBO).1
  have hdisj : Disjoint O (B \ O) := by
    rw [Finset.disjoint_left]
    intro u huO huBO
    exact (Finset.mem_sdiff.mp huBO).2 huO
  have hrem : 0 ≤ ∑ u ∈ B \ O, vertexCharge G D u := by
    apply Finset.sum_nonneg
    intro u hu
    exact paper11_charge_nonnegative_on_B G hCan hmax
      (Finset.mem_sdiff.mp hu).1
  calc
    _ ≤ (∑ u ∈ O, vertexCharge G D u) +
        ∑ u ∈ B \ O, vertexCharge G D u := by linarith
    _ = ∑ u ∈ B, vertexCharge G D u := by
      calc
        _ = ∑ u ∈ O ∪ (B \ O), vertexCharge G D u :=
          (Finset.sum_union hdisj).symm
        _ = ∑ u ∈ B, vertexCharge G D u := by
          congr 1
          exact hdecomp.symm
end C6BipartiteDomination
