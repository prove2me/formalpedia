-- Prove2me | solution 1 for C6BipartiteDomination.paper11_external_charge_sum_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:52.714739+00:00
-- url     : https://prove2.me/submissions/a0021724-6c83-4bd8-876a-00b01deda10f

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11_nonnegative_charge_partition
import Theorems.Thm_C6BipartiteDomination_paper11_all_compensation_subset_nonnegative

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
    (∑ w ∈ SPart G D, externalCharge G D w) =
      (∑ w ∈ paper11NegativeSupports G D, externalCharge G D w) +
      (∑ q ∈ paper11AllCompensation G D hCan hmax,
        externalCharge G D q) +
      (∑ q ∈ paper11NonnegativeSupports G D \
        paper11AllCompensation G D hCan hmax, externalCharge G D q) := by
  classical
  let N := paper11NegativeSupports G D
  let P := paper11NonnegativeSupports G D
  let C := paper11AllCompensation G D hCan hmax
  have hNP : SPart G D = N ∪ P := by simpa [N, P] using
    paper11_nonnegative_charge_partition G hCan hmax
  have hdisjNP : Disjoint N P := by
    rw [Finset.disjoint_left]
    intro w hwN hwP
    exact (Finset.mem_sdiff.mp hwP).2 hwN
  have hCP : C ⊆ P := by simpa [C, P] using
    paper11_all_compensation_subset_nonnegative G hCan hmax
  have hsplitP : P = C ∪ (P \ C) := by
    ext q
    constructor
    · intro hq
      by_cases hqC : q ∈ C
      · exact Finset.mem_union_left _ hqC
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hq, hqC⟩)
    · intro hq
      rcases Finset.mem_union.mp hq with hqC | hqPC
      · exact hCP hqC
      · exact (Finset.mem_sdiff.mp hqPC).1
  have hdisjCP : Disjoint C (P \ C) := by
    rw [Finset.disjoint_left]
    intro q hqC hqPC
    exact (Finset.mem_sdiff.mp hqPC).2 hqC
  have hsumP : (∑ q ∈ P, externalCharge G D q) =
      (∑ q ∈ C, externalCharge G D q) +
        ∑ q ∈ P \ C, externalCharge G D q := by
    calc
      _ = ∑ q ∈ C ∪ (P \ C), externalCharge G D q := by
        apply Finset.sum_congr hsplitP
        intro q hq
        rfl
      _ = _ := Finset.sum_union hdisjCP
  calc
    _ = ∑ w ∈ N ∪ P, externalCharge G D w := by rw [hNP]
    _ = (∑ w ∈ N, externalCharge G D w) +
        ∑ w ∈ P, externalCharge G D w := Finset.sum_union hdisjNP
    _ = (∑ w ∈ N, externalCharge G D w) +
        ((∑ q ∈ C, externalCharge G D q) +
          ∑ q ∈ P \ C, externalCharge G D q) := by
      rw [hsumP]
    _ = (∑ w ∈ N, externalCharge G D w) +
        (∑ q ∈ C, externalCharge G D q) +
          ∑ q ∈ P \ C, externalCharge G D q := by ring
end C6BipartiteDomination
