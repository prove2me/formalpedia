-- Prove2me | solution 1 for C6BipartiteDomination.paper9_repair_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:21.965378+00:00
-- url     : https://prove2.me/submissions/539959df-721c-49ba-912d-0e15bdcdd20c

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
    {u : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w) :
    T.card ≤ 2 := by
  classical
  have hThigh : ∀ w ∈ T, 3 ≤ kCharge G D w := by
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
  have hTthree : 3 ≤ T.card := by omega
  have hxzero : xCharge G D u = 0 := by omega
  obtain ⟨w, hwT⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u :=
    ⟨hTrepair w hwT,
      paperChosenRepairSet_legal G hCan hmax (hTsub hwT)
        (hTnegative w hwT) u (hTrepair w hwT)⟩
  have hLbound := lemma_8_5_compensation_lower_bound G hCan hmax
    (hTsub hwT) (hTnegative w hwT) hChosen
  have hLpos : 0 <
      (sharedCompensation G D (supportX G D w) u).card := by
    rw [hxzero] at hLbound
    have hk := hThigh w hwT
    omega
  let L := sharedCompensation G D (supportX G D w) u
  obtain ⟨q, hqL⟩ := Finset.card_pos.mp (by simpa [L] using hLpos)
  have hX : supportX G D w ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hLinc := paper9_shared_set_incidence G hX huB
  have hLsub : L ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    simpa [L] using hLinc.1
  have hdisj : Disjoint T L := by
    apply hLinc.2 T
    exact fun v hv => le_trans (by decide : 2 ≤ 3) (hThigh v hv)
  have hTL := paper9_union_resource_bound G hTneighbors hLsub hdisj
  rw [hxzero] at hbudget
  have hLcard : 1 ≤ L.card := by
    have : 0 < L.card := by simpa [L] using hLpos
    omega
  omega
end C6BipartiteDomination
