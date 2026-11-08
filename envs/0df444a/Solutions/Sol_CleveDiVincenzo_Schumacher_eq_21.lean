-- Prove2me | solution 1 for CleveDiVincenzo.Schumacher.eq_21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:53:23.649963+00:00
-- url     : https://prove2.me/submissions/70ab1421-d3a0-4638-98cc-f119a843717e

import Mathlib
import Definitions.Def_CleveDiVincenzo_Schumacher_schumacher

namespace Aux_Schumacher_bij
open CleveDiVincenzo.Schumacher

def bits (n z : ℕ) : Finset ℕ := (Finset.range n).filter (fun k => z.testBit k = true)

theorem weight_eq (x N : ℕ) (hx : x < 2 ^ N) : weight x = (bits N x).card := by
  have h1 : weight x = (((List.range (Nat.log2 x + 1)).filter (fun k => x.testBit k)).toFinset).card := by
    rw [List.toFinset_card_of_nodup ((List.nodup_range).filter _)]; rfl
  rw [h1, List.toFinset_filter, List.toFinset_range]
  unfold bits
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  have hL := @Nat.lt_log2_self x
  constructor
  · rintro ⟨_, hb⟩
    refine ⟨?_, by simpa using hb⟩
    by_contra hk; push_neg at hk
    have := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right two_pos hk))
    simp_all
  · rintro ⟨_, hb⟩
    refine ⟨?_, by simpa using hb⟩
    by_contra hk; push_neg at hk
    have := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hL (Nat.pow_le_pow_right two_pos hk))
    simp_all

theorem bits_inj (n : ℕ) (z z' : ℕ) (hz : z < 2 ^ n) (hz' : z' < 2 ^ n) (h : bits n z = bits n z') :
    z = z' := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < n
  · have := congrArg (fun S => k ∈ S) h
    simp only [bits, Finset.mem_filter, Finset.mem_range, eq_iff_iff] at this
    cases h1 : z.testBit k <;> cases h2 : z'.testBit k <;> simp_all
  · push_neg at hk
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right two_pos hk)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz' (Nat.pow_le_pow_right two_pos hk))]

theorem bits_surj (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n) :
    ∃ z, z < 2 ^ n ∧ bits n z = S := by
  have := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range (2 ^ n))
    (t := (Finset.range n).powerset) (fun z _ => bits n z)
    (fun z _ => by simp only [Finset.mem_powerset]; exact Finset.filter_subset _ _)
    (fun a b ha hb h => bits_inj n a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h)
    (by simp)
  obtain ⟨z, hz, h⟩ := this S (Finset.mem_powerset.mpr hS)
  exact ⟨z, Finset.mem_range.mp hz, h.symm⟩

theorem count_weight (n m : ℕ) :
    ((Finset.range (2 ^ n)).filter (fun z => weight z = m)).card = n.choose m := by
  rw [show n.choose m = ((Finset.range n).powersetCard m).card by
    rw [Finset.card_powersetCard, Finset.card_range]]
  apply Finset.card_bij (fun z _ => bits n z)
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_range] at hz
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, by rw [← weight_eq z n hz.1]; exact hz.2⟩
  · intro a ha b hb h
    simp only [Finset.mem_filter, Finset.mem_range] at ha hb
    exact bits_inj n a b ha.1 hb.1 h
  · intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨z, hz, h⟩ := bits_surj n S hS.1
    refine ⟨z, ?_, h⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hz, by rw [weight_eq z n hz, h, hS.2]⟩

theorem weight_le (n x : ℕ) (hx : x < 2 ^ n) : weight x ≤ n := by
  rw [weight_eq x n hx]
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem index_lt (n x : ℕ) (hx : x < 2 ^ n) : index n x < n.choose (weight x) := by
  rw [← count_weight n (weight x)]
  unfold index
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, ?_, ?_⟩
    · simp [hx]
    · simp
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.1⟩

theorem index_strict (n x y : ℕ) (hy : y < 2 ^ n) (hw : weight x = weight y) (hxy : x < y) :
    index n x < index n y := by
  unfold index
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨lt_trans hxy hy, hw, hxy⟩
    · simp
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.1.trans hw, lt_trans hz.2.2 hxy⟩

theorem blockStart_succ (n m : ℕ) : blockStart n (m + 1) = blockStart n m + n.choose m := by
  unfold blockStart; rw [Finset.sum_range_succ]

theorem blockStart_mono (n : ℕ) {a b : ℕ} (h : a ≤ b) : blockStart n a ≤ blockStart n b := by
  unfold blockStart
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr h)

theorem sch_lt (n x : ℕ) (hx : x < 2 ^ n) : schumacher n x < blockStart n (weight x + 1) := by
  rw [blockStart_succ]; unfold schumacher
  have := index_lt n x hx; omega

end Aux_Schumacher_bij

open CleveDiVincenzo.Schumacher Aux_Schumacher_bij in
theorem solution (n x : ℕ) (hx : x < 2 ^ n) :
    blockStart n (weight x) ≤ schumacher n x ∧
      schumacher n x < blockStart n (weight x + 1) := by
  refine ⟨?_, sch_lt n x hx⟩
  unfold schumacher
  omega
