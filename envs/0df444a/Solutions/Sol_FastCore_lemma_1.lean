-- Prove2me | solution 1 for FastCore.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:40:36.980215+00:00
-- url     : https://prove2.me/submissions/87d88979-81ad-4271-8bda-cca18ceb8f11

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_InCore
import Definitions.Def_FastCore_IsWelfareMaximizing
import Definitions.Def_FastCore_OutcomeInCore

open ComplementFreeCA.CFRounding (IsAllocation welfare)

open FastCore in
theorem solution {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : InCore b π) {x : Fin n → Finset (Fin m)} (hx : IsWelfareMaximizing b x) :
    OutcomeInCore b x (fun i => b i (x i) - π i) := by
  classical
  have hwN : w b Finset.univ = welfare b x := by
    unfold w
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun y hy => hx.2 y (Finset.mem_filter.mp hy).2.1
    · exact Finset.le_sup' (welfare b) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hx.1, fun i hi => absurd (Finset.mem_univ i) hi⟩)
  have h3 : ∀ i, 0 ≤ b i (x i) - (b i (x i) - π i) := fun i => by
    rw [_root_.sub_sub_cancel]; exact hπ.1 i
  refine ⟨hx.1, fun i => ?_, h3, fun S => ?_⟩
  · -- π i ≤ b i (x i)
    let x' : Fin n → Finset (Fin m) := fun j => if j = i then ∅ else x j
    have hx'mem : x' ∈ Finset.univ.filter (fun y : Fin n → Finset (Fin m) =>
        IsAllocation y ∧ ∀ j, j ∉ Finset.univ.erase i → y j = ∅) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro j j' hjj'
        simp only [x']
        split_ifs
        · exact Finset.disjoint_empty_left _
        · exact Finset.disjoint_empty_left _
        · exact Finset.disjoint_empty_right _
        · exact hx.1 j j' hjj'
      · intro j hj
        have : j = i := by
          by_contra h
          exact hj (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩)
        simp only [x', if_pos this]
    have hle : welfare b x' ≤ w b (Finset.univ.erase i) := Finset.le_sup' (welfare b) hx'mem
    have hwx : welfare b x = b i (x i) + ∑ j ∈ Finset.univ.erase i, b j (x j) := by
      unfold welfare
      exact (Finset.add_sum_erase Finset.univ (fun j => b j (x j)) (Finset.mem_univ i)).symm
    have hwx' : welfare b x' = ∑ j ∈ Finset.univ.erase i, b j (x j) := by
      unfold welfare
      rw [← Finset.add_sum_erase Finset.univ (fun j => b j (x' j)) (Finset.mem_univ i)]
      have h0 : b i (x' i) = 0 := by simp only [x', if_pos rfl]; exact hb.1 i
      rw [h0, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      simp only [x', if_neg (Finset.ne_of_mem_erase hj)]
    have hcore := hπ.2 (Finset.univ.erase i)
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hwN] at hcore
    show 0 ≤ b i (x i) - π i
    linarith
  · show w b S - ∑ i ∈ S, (b i (x i) - (b i (x i) - π i)) ≤ ∑ i, (b i (x i) - π i)
    simp only [_root_.sub_sub_cancel]
    rw [Finset.sum_sub_distrib]
    have hcore := hπ.2 S
    rw [hwN] at hcore
    unfold welfare at hcore
    linarith
