-- Prove2me | solution 1 for CleveDiVincenzo.Schumacher.eq_23
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:49:41.254238+00:00
-- url     : https://prove2.me/submissions/58114552-368d-4e36-a0b3-5dfce1515b26

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher

namespace CleveDiVincenzo.Schumacher.Aux_CS

open CleveDiVincenzo.Schumacher

theorem weight_eq (x : ℕ) : weight x = (Nat.bitIndices x).toFinset.card := by
  unfold weight
  have hnd : ((List.range (Nat.log2 x + 1)).filter fun k => x.testBit k).Nodup :=
    (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext k
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Nat.mem_bitIndices]
  constructor
  · intro h; exact h.2
  · intro h
    refine ⟨?_, h⟩
    have h2 : 2 ^ k ≤ x := Nat.two_pow_le_of_mem_bitIndices (Nat.mem_bitIndices.mpr h)
    have : k ≤ Nat.log2 x := by
      rw [Nat.log2_eq_log_two]
      exact Nat.le_log_of_pow_le (by norm_num) h2
    omega

theorem lt_iff_subset (x m : ℕ) : x < 2 ^ m ↔ (Nat.bitIndices x).toFinset ⊆ Finset.range m := by
  constructor
  · intro h k hk
    rw [List.mem_toFinset] at hk
    have h2 := Nat.two_pow_le_of_mem_bitIndices hk
    rw [Finset.mem_range]
    by_contra hc
    push_neg at hc
    have : 2 ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
    omega
  · intro h
    rw [← Finset.sum_toFinset_bitIndices_two_pow x]
    apply Nat.geomSum_lt (le_refl 2)
    intro k hk
    exact Finset.mem_range.mp (h hk)

theorem count (m w : ℕ) :
    ((Finset.range (2 ^ m)).filter fun z => weight z = w).card = m.choose w := by
  have hch : m.choose w = (Finset.powersetCard w (Finset.range m)).card := by
    rw [Finset.card_powersetCard, Finset.card_range]
  rw [hch]
  apply Finset.card_nbij' (fun z => (Nat.bitIndices z).toFinset) (fun s => ∑ i ∈ s, 2 ^ i)
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hz
    simp only [Finset.mem_coe, Finset.mem_powersetCard]
    exact ⟨(lt_iff_subset z m).mp hz.1, by rw [← weight_eq]; exact hz.2⟩
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_powersetCard] at hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · rw [lt_iff_subset, Finset.toFinset_bitIndices_sum_two_pow]; exact hs.1
    · rw [weight_eq, Finset.toFinset_bitIndices_sum_two_pow]; exact hs.2
  · intro z _
    exact Finset.sum_toFinset_bitIndices_two_pow z
  · intro s _
    exact Finset.toFinset_bitIndices_sum_two_pow s

end CleveDiVincenzo.Schumacher.Aux_CS

open CleveDiVincenzo.Schumacher CleveDiVincenzo.Schumacher.Aux_CS in
theorem solution (n p x' : ℕ) (hp : p < n) (hx' : x' < 2 ^ (n - p - 1)) :
    let x := 2 ^ (n - p - 1) + x'
    (n - p - 1).choose (weight x) ≤ index n x ∧ index n x < (n - p).choose (weight x) := by
  intro x
  set k := n - p - 1 with hk
  have hnp : n - p = k + 1 := by omega
  have hkn : k ≤ n := by omega
  have hxlt : x < 2 ^ (k + 1) := by
    show 2 ^ k + x' < 2 ^ (k + 1)
    rw [pow_succ]; omega
  have hxge : 2 ^ k ≤ x := by show 2 ^ k ≤ 2 ^ k + x'; omega
  rw [hnp]
  constructor
  · rw [← count k (weight x)]
    unfold index
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_range] at hz ⊢
    have h2 : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hkn
    exact ⟨by omega, hz.2, by omega⟩
  · rw [← count (k + 1) (weight x)]
    unfold index
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hxlt, by trivial⟩
      · simp only [Finset.mem_filter, Finset.mem_range, not_and]
        intro _ _; exact lt_irrefl x
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_range] at hz ⊢
      exact ⟨by omega, hz.2.1⟩
