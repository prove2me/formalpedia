-- Prove2me | solution 1 for FairShareAlmostAll.Slack.Supplement.no_five_target_bundles
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:05:59.139238+00:00
-- url     : https://prove2.me/submissions/a903cbf0-aa9a-45ea-b213-c13a1720d16f

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Supplement_ThirteenGoods

namespace FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding

def fsWN : Fin 13 → ℕ := ![137, 135, 119, 79, 77, 76, 54, 50, 49, 10, 9, 8, 6]

lemma fs_addVal_eq (T : Finset (Fin 13)) :
    addVal thirteenValue T = ((∑ j ∈ T, fsWN j : ℕ) : ℝ) := by
  unfold addVal
  push_cast
  refine Finset.sum_congr rfl (fun j _ => ?_)
  fin_cases j <;> simp [thirteenValue, fsWN]

lemma fs_mono {S T : Finset (Fin 13)} (h : S ⊆ T) : ∑ j ∈ S, fsWN j ≤ ∑ j ∈ T, fsWN j :=
  Finset.sum_le_sum_of_subset h

lemma fs_pair_le {S : Finset (Fin 13)} {x y : Fin 13} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) :
    fsWN x + fsWN y ≤ ∑ j ∈ S, fsWN j := by
  have hsub : ({x, y} : Finset (Fin 13)) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have := fs_mono hsub
  rwa [Finset.sum_pair hxy] at this

lemma fs_total : ∑ j ∈ (Finset.univ : Finset (Fin 13)), fsWN j = 809 := by
  simp [Fin.sum_univ_succ, fsWN]

lemma fs_two_bundle (S : Finset (Fin 13)) (h2 : 2 ∈ S) (h : 153 ≤ ∑ j ∈ S, fsWN j) :
    168 ≤ ∑ j ∈ S, fsWN j := by
  by_cases hs : S ⊆ {2, 9, 10, 11, 12}
  · have h1 := fs_mono hs
    have h' : ∑ j ∈ ({2, 9, 10, 11, 12} : Finset (Fin 13)), fsWN j = 152 := by decide
    omega
  · obtain ⟨x, hxS, hx⟩ := Finset.not_subset.mp hs
    have hne : (2 : Fin 13) ≠ x := by rintro rfl; simp at hx
    have := fs_pair_le h2 hxS hne
    generalize ∑ j ∈ S, fsWN j = s at this h ⊢
    fin_cases x <;> simp [fsWN] at this hx ⊢ <;> omega

lemma fs_zero_small (S : Finset (Fin 13)) (h0 : 0 ∈ S) (h : ∑ j ∈ S, fsWN j ≤ 182) :
    S ⊆ {0, 9, 10, 11, 12} := by
  intro x hx
  by_contra hn
  have hne : (0 : Fin 13) ≠ x := by rintro rfl; simp at hn
  have := fs_pair_le h0 hx hne
  generalize ∑ j ∈ S, fsWN j = s at this h
  fin_cases x <;> simp [fsWN] at this hn <;> omega

lemma fs_one_small (S : Finset (Fin 13)) (h1 : 1 ∈ S) (h : ∑ j ∈ S, fsWN j ≤ 182) :
    S ⊆ {1, 9, 10, 11, 12} := by
  intro x hx
  by_contra hn
  have hne : (1 : Fin 13) ≠ x := by rintro rfl; simp at hn
  have := fs_pair_le h1 hx hne
  generalize ∑ j ∈ S, fsWN j = s at this h
  fin_cases x <;> simp [fsWN] at this hn <;> omega

lemma fs_small_pair (S T : Finset (Fin 13)) (hS : S ⊆ {0, 9, 10, 11, 12})
    (hT : T ⊆ {1, 9, 10, 11, 12}) (hd : Disjoint S T)
    (h1 : 153 ≤ ∑ j ∈ S, fsWN j) (h2 : 153 ≤ ∑ j ∈ T, fsWN j) : False := by
  have hu := Finset.sum_union (f := fsWN) hd
  have hsub : S ∪ T ⊆ {0, 1, 9, 10, 11, 12} := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · have := hS h; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; tauto
    · have := hT h; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢; tauto
  have hm := fs_mono hsub
  have hv : ∑ j ∈ ({0, 1, 9, 10, 11, 12} : Finset (Fin 13)), fsWN j = 305 := by decide
  omega

theorem no_five_target_bundles (B : Fin 5 → Finset (Fin 13)) (hB : PartialAllocation B) :
    ∃ j, addVal thirteenValue (B j) < 153 := by
  by_contra hcon
  push Not at hcon
  have hf : ∀ j, 153 ≤ ∑ i ∈ B j, fsWN i := by
    intro j
    have := hcon j
    rw [fs_addVal_eq] at this
    exact_mod_cast this
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 5))) B := by
    intro i _ k _ hik
    exact hB i k hik
  have hsumU : ∑ j, ∑ i ∈ B j, fsWN i = ∑ i ∈ Finset.univ.biUnion B, fsWN i :=
    (Finset.sum_biUnion hdisj).symm
  have hle : ∑ j, ∑ i ∈ B j, fsWN i ≤ 809 := by
    rw [hsumU, ← fs_total]
    exact fs_mono (Finset.subset_univ _)
  have mem : ∀ g : Fin 13, 809 < 765 + fsWN g → ∃ a, g ∈ B a := by
    intro g hg
    by_contra hno
    push Not at hno
    have hsub : Finset.univ.biUnion B ⊆ Finset.univ.erase g := by
      intro x hx
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hx
      exact hno a ha
    have h1 := fs_mono hsub
    have h2 := Finset.sum_erase_add (s := Finset.univ) (f := fsWN) (Finset.mem_univ g)
    rw [fs_total] at h2
    have h5 : 765 ≤ ∑ j, ∑ i ∈ B j, fsWN i := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) => hf j)
      simpa using this
    omega
  obtain ⟨a, ha⟩ := mem 0 (by decide)
  obtain ⟨b, hb⟩ := mem 1 (by decide)
  obtain ⟨c, hc⟩ := mem 2 (by decide)
  have K1 := fs_two_bundle (B c) hc (hf c)
  have K2ab : a = b → 272 ≤ ∑ i ∈ B a, fsWN i := by
    rintro rfl
    have := fs_pair_le ha hb (by decide)
    simpa [fsWN] using this
  have K2ac : a = c → 256 ≤ ∑ i ∈ B a, fsWN i := by
    rintro rfl
    have := fs_pair_le ha hc (by decide)
    simpa [fsWN] using this
  have K2bc : b = c → 254 ≤ ∑ i ∈ B b, fsWN i := by
    rintro rfl
    have := fs_pair_le hb hc (by decide)
    simpa [fsWN] using this
  have K3 : a ≠ b → 183 ≤ ∑ i ∈ B a, fsWN i ∨ 183 ≤ ∑ i ∈ B b, fsWN i := by
    intro hab
    by_contra hh
    push Not at hh
    have sa := fs_zero_small (B a) ha (by omega)
    have sb := fs_one_small (B b) hb (by omega)
    exact fs_small_pair (B a) (B b) sa sb (hB a b hab) (hf a) (hf b)
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have h3 := hf 3
  have h4 := hf 4
  rw [Fin.sum_univ_five] at hle
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at K1 K2ab K2ac K2bc K3 <;> omega

end FairShareAlmostAll.Slack.Supplement

open FairShareAlmostAll.Slack AnyPriceShare.Bidding FairShareAlmostAll.Slack.Supplement in
theorem solution (B : Fin 5 → Finset (Fin 13)) (hB : PartialAllocation B) :
    ∃ j, addVal thirteenValue (B j) < 153 := by
  first
  | exact FairShareAlmostAll.Slack.Supplement.no_five_target_bundles
  | exact FairShareAlmostAll.Slack.Supplement.no_five_target_bundles ..
  | (intros; apply FairShareAlmostAll.Slack.Supplement.no_five_target_bundles <;> assumption)
