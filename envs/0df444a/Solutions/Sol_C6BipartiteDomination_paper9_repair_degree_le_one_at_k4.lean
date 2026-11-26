-- Prove2me | solution 1 for C6BipartiteDomination.paper9_repair_degree_le_one_at_k4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:23.29314+00:00
-- url     : https://prove2.me/submissions/a7ff4ead-540a-4a11-90c1-ccacbabbfa1d

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal
import Theorems.Thm_C6BipartiteDomination_paper9_sCharge_add_xCharge_le_three
import Theorems.Thm_C6BipartiteDomination_paper9_shared_set_incidence
import Theorems.Thm_C6BipartiteDomination_paper9_union_resource_bound
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification
import Theorems.Thm_C6BipartiteDomination_lemma_8_5_compensation_lower_bound
import Theorems.Thm_C6BipartiteDomination_mem_supportX


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
    T.card ≤ 1 := by
  classical
  have hThigh : ∀ w ∈ T, 2 ≤ kCharge G D w := by
    intro w hw
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        (hTsub hw) (hTnegative w hw) with h | h | h <;> omega
  have hTadj : ∀ w ∈ T, G.Adj w u := by
    intro w hw
    have hLegal := paperChosenRepairSet_legal G hCan hmax
      (hTsub hw) (hTnegative w hw) u (hTrepair w hw)
    exact hLegal.2.1
  have hTneighbors : T ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hTsub hw, (hTadj w hw).symm⟩
  have hTleS : T.card ≤ sCharge G D u := by
    have hcard := Finset.card_le_card hTneighbors
    simpa [sCharge, degreeTo] using hcard
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax huB
  by_contra hnot
  have hTtwo : 2 ≤ T.card := by omega
  have hChosen : ChosenRepairRelation G D w₄
      (paperChosenRepairSet G D hCan hmax w₄) u :=
    ⟨hTrepair w₄ hw₄,
      paperChosenRepairSet_legal G hCan hmax (hTsub hw₄)
        (hTnegative w₄ hw₄) u (hTrepair w₄ hw₄)⟩
  have hLbound := lemma_8_5_compensation_lower_bound G hCan hmax
    (hTsub hw₄) (hTnegative w₄ hw₄) hChosen
  have hX : supportX G D w₄ ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w₄ z).mp hz |>.1
  let L := sharedCompensation G D (supportX G D w₄) u
  have hLbound' : 2 ≤ xCharge G D u + L.card := by
    simpa [L, hk₄] using hLbound
  have hLsub : L ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    exact (paper9_shared_set_incidence G hX huB).1
  have hdisj : Disjoint T L := by
    apply (paper9_shared_set_incidence G hX huB).2 T
    exact hThigh
  have hTL := paper9_union_resource_bound G hTneighbors hLsub hdisj
  by_cases hx0 : xCharge G D u = 0
  · have hLtwo : 2 ≤ L.card := by
      rw [hx0] at hLbound'
      omega
    omega
  · by_cases hx1 : xCharge G D u = 1
    · have hLone : 1 ≤ L.card := by
        rw [hx1] at hLbound'
        omega
      omega
    · have hxge2 : 2 ≤ xCharge G D u := by omega
      omega
end C6BipartiteDomination
