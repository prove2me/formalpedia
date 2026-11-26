-- Prove2me | solution 1 for C6BipartiteDomination.paper11_k4_separate_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:17.039252+00:00
-- url     : https://prove2.me/submissions/feab5df4-0bcb-411f-a38c-e5614dfa34e1

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_mem_paper11K4Supports
import Theorems.Thm_C6BipartiteDomination_paper11_chosen_profile
import Theorems.Thm_C6BipartiteDomination_paper9_repair_degree_eq_one_at_k4
import Theorems.Thm_C6BipartiteDomination_paper9_single_repair_resource_bound
import Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    ∃ u v, u ≠ v ∧
      u ∈ paperChosenRepairSet G D hCan hmax w ∧
      v ∈ paperChosenRepairSet G D hCan hmax w ∧
      (paper11NegativeIncidentSupports G D hCan hmax u).card = 1 ∧
      (paper11NegativeIncidentSupports G D hCan hmax v).card = 1 ∧
      8 ≤ vertexCharge G D u +
        ∑ q ∈ sharedCompensation G D (supportX G D w) u,
          externalCharge G D q ∧
      8 ≤ vertexCharge G D v +
        ∑ q ∈ sharedCompensation G D (supportX G D w) v,
          externalCharge G D q := by
  classical
  have hwInfo := mem_paper11K4Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hwInfo.1 hwInfo.2.1
  have hcard : (paperChosenRepairSet G D hCan hmax w).card = 2 := by
    rcases hprofile with h | h | h
    · omega
    · omega
    · exact h.2.2
  let R := paperChosenRepairSet G D hCan hmax w
  obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hcard]; omega)
  have hEraseCard : (R.erase u).card = 1 := by
    calc
      (R.erase u).card = R.card - 1 := Finset.card_erase_of_mem hu
      _ = 1 := by dsimp [R]; rw [hcard]
  obtain ⟨v, hvEraseEq⟩ := Finset.card_eq_one.mp hEraseCard
  have hvErase : v ∈ R.erase u := by rw [hvEraseEq]; simp
  have hvR := (Finset.mem_erase.mp hvErase).2
  have hne : u ≠ v := (Finset.mem_erase.mp hvErase).1.symm
  have huChosen : u ∈ paperChosenRepairSet G D hCan hmax w := hu
  have hvChosen : v ∈ paperChosenRepairSet G D hCan hmax w := hvR
  have huLegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u huChosen
  have hvLegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 v hvChosen
  let T_u := paper11NegativeIncidentSupports G D hCan hmax u
  let T_v := paper11NegativeIncidentSupports G D hCan hmax v
  have hwTu : w ∈ T_u := by
    simp [T_u, paper11NegativeIncidentSupports, paper11NegativeSupports,
      hwInfo.1, hwInfo.2.1, huChosen]
  have hwTv : w ∈ T_v := by
    simp [T_v, paper11NegativeIncidentSupports, paper11NegativeSupports,
      hwInfo.1, hwInfo.2.1, hvChosen]
  have hTuSub : T_u ⊆ SPart G D := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hTvSub : T_v ⊆ SPart G D := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hTuNeg : ∀ x ∈ T_u, externalCharge G D x < 0 := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hTvNeg : ∀ x ∈ T_v, externalCharge G D x < 0 := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hTuChosen : ∀ x ∈ T_u, u ∈ paperChosenRepairSet G D hCan hmax x := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hTvChosen : ∀ x ∈ T_v, v ∈ paperChosenRepairSet G D hCan hmax x := by
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  have hTuCard := paper9_repair_degree_eq_one_at_k4 G hCan hmax huLegal.1
    T_u hTuSub hTuNeg hTuChosen hwTu hwInfo.2.2
  have hTvCard := paper9_repair_degree_eq_one_at_k4 G hCan hmax hvLegal.1
    T_v hTvSub hTvNeg hTvChosen hwTv hwInfo.2.2
  have hChosenU : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u := ⟨huChosen, huLegal⟩
  have hChosenV : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) v := ⟨hvChosen, hvLegal⟩
  have hBoundU := paper9_single_repair_resource_bound G hCan hmax huLegal.1
    hwInfo.1 hwInfo.2.1 hChosenU (Or.inr hwInfo.2.2)
  have hBoundV := paper9_single_repair_resource_bound G hCan hmax hvLegal.1
    hwInfo.1 hwInfo.2.1 hChosenV (Or.inr hwInfo.2.2)
  have h8U : 8 ≤ vertexCharge G D u +
      ∑ q ∈ sharedCompensation G D (supportX G D w) u,
        externalCharge G D q := by
    rcases hBoundU with h3 | h4
    · omega
    · exact h4.2
  have h8V : 8 ≤ vertexCharge G D v +
      ∑ q ∈ sharedCompensation G D (supportX G D w) v,
        externalCharge G D q := by
    rcases hBoundV with h3 | h4
    · omega
    · exact h4.2
  exact ⟨u, v, hne, huChosen, hvChosen, by simpa [T_u] using hTuCard,
    by simpa [T_v] using hTvCard, h8U, h8V⟩
end C6BipartiteDomination
