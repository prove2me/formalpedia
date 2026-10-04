-- Prove2me | solution 1 for BinPacking.FirstFit.early_items_exceed_coarseness
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T07:39:32.713729+00:00
-- url     : https://prove2.me/submissions/4a2a25e7-ff45-47d2-b3f6-7a34490fe2b7

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model

set_option autoImplicit false

namespace DA7E5FD9
open BinPacking.FirstFit

lemma placeAt_len_ge (S : List (List ℝ)) (c : ℕ) (a : ℝ) :
    S.length ≤ (placeAt S c a).length := by
  unfold placeAt; split_ifs <;> simp

lemma placeAt_len_eq (S : List (List ℝ)) (c : ℕ) (a : ℝ) (hc : c < S.length) :
    (placeAt S c a).length = S.length := by
  unfold placeAt; simp [hc]

lemma placeAt_new (S : List (List ℝ)) (c : ℕ) (a : ℝ) (hc : ¬ c < S.length) :
    placeAt S c a = S ++ [[a]] := by
  unfold placeAt; simp [hc]

lemma placeAt_mono (S : List (List ℝ)) (c : ℕ) (a : ℝ) (ha : 0 ≤ a) (j : ℕ)
    (hj : j < S.length) :
    (S.getD j []).sum ≤ ((placeAt S c a).getD j []).sum := by
  unfold placeAt
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_mapIdx]
    split_ifs <;> simp [ha]
  · rw [List.getD_eq_getElem _ _ hj,
      List.getD_eq_getElem _ _ (by simp; omega)]
    rw [List.getElem_append_left hj]

lemma foldl_mono (ch : List (List ℝ) → ℝ → ℕ) :
    ∀ (M : List ℝ) (S : List (List ℝ)), (∀ a ∈ M, 0 ≤ a) →
      S.length ≤ (M.foldl (fun bins a => placeAt bins (ch bins a) a) S).length ∧
      ∀ j < S.length, (S.getD j []).sum ≤
        ((M.foldl (fun bins a => placeAt bins (ch bins a) a) S).getD j []).sum := by
  intro M
  induction M with
  | nil => intro S _; simp
  | cons b M ih =>
    intro S hM
    simp only [List.foldl_cons]
    have hb : 0 ≤ b := hM b (by simp)
    obtain ⟨h1, h2⟩ := ih (placeAt S (ch S b) b) (fun a ha => hM a (by simp [ha]))
    refine ⟨le_trans (placeAt_len_ge S _ b) h1, fun j hj => ?_⟩
    exact le_trans (placeAt_mono S _ b hb j hj)
      (h2 j (lt_of_lt_of_le hj (placeAt_len_ge S _ b)))

def Half (S : List (List ℝ)) : Prop :=
  ∀ j' j : ℕ, j < S.length → j' < j → (S.getD j' []).sum ≤ 1 / 2 → 1 / 2 < (S.getD j []).sum

def GoodCh (ch : List (List ℝ) → ℝ → ℕ) : Prop :=
  ∀ (S : List (List ℝ)) (a : ℝ), ch S a ≤ S.length ∧
    (ch S a = S.length → ∀ j < S.length, 1 < (S.getD j []).sum + a)

lemma half_step (ch : List (List ℝ) → ℝ → ℕ) (hg : GoodCh ch) (S : List (List ℝ)) (a : ℝ)
    (ha : 0 < a) (hS : Half S) : Half (placeAt S (ch S a) a) := by
  intro j' j hj hjj hle
  have hj'S : ∀ (h : j < S.length), 1 / 2 < ((placeAt S (ch S a) a).getD j []).sum := by
    intro h
    have hm' := placeAt_mono S (ch S a) a ha.le j' (lt_trans hjj h)
    have hm := placeAt_mono S (ch S a) a ha.le j h
    have := hS j' j h hjj (le_trans hm' hle)
    linarith
  by_cases h : j < S.length
  · exact hj'S h
  · by_cases hc : ch S a < S.length
    · rw [placeAt_len_eq S _ a hc] at hj; exact absurd hj h
    · have hcl : ch S a = S.length := le_antisymm (hg S a).1 (not_lt.mp hc)
      have hnew := placeAt_new S _ a hc
      rw [hnew] at hj
      simp at hj
      have hjS : j = S.length := by omega
      have hj'lt : j' < S.length := by omega
      have hfit := (hg S a).2 hcl j' hj'lt
      have hm' := placeAt_mono S (ch S a) a ha.le j' hj'lt
      rw [hnew] at hm' ⊢
      rw [hjS, List.getD_eq_getElem _ _ (by simp)]
      simp
      rw [hnew] at hle
      linarith

lemma half_foldl (ch : List (List ℝ) → ℝ → ℕ) (hg : GoodCh ch) :
    ∀ (M : List ℝ) (S : List (List ℝ)), (∀ a ∈ M, 0 < a) → Half S →
      Half (M.foldl (fun bins a => placeAt bins (ch bins a) a) S) := by
  intro M
  induction M with
  | nil => intro S _ h; simpa using h
  | cons b M ih =>
    intro S hM hS
    simp only [List.foldl_cons]
    exact ih _ (fun a ha => hM a (by simp [ha]))
      (half_step ch hg S b (hM b (by simp)) hS)

lemma half_nil : Half [] := by
  intro j' j hj; simp at hj

lemma ff_good : GoodCh ffChoice := by
  intro S a
  refine ⟨List.findIdx_le_length, fun h j hj => ?_⟩
  unfold ffChoice at h
  rw [List.findIdx_eq_length] at h
  have := h (S[j]) (List.getElem_mem hj)
  rw [List.getD_eq_getElem _ _ hj]
  simp at this
  linarith

lemma bf_good : GoodCh bfChoice := by
  intro S a
  refine ⟨List.findIdx_le_length, fun h j hj => ?_⟩
  unfold bfChoice at h
  rw [List.findIdx_eq_length] at h
  rw [List.getD_eq_getElem _ _ hj]
  by_contra hcon
  push Not at hcon
  have hne : (S.toFinset.filter (fun B : List ℝ => B.sum + a ≤ 1)).Nonempty :=
    ⟨S[j], by simp [List.getElem_mem hj]; linarith⟩
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image _ (fun B : List ℝ => B.sum) hne
  simp only [Finset.mem_filter, List.mem_toFinset] at hB
  have := h B hB.1
  simp only [decide_eq_false_iff_not, not_and, not_forall] at this
  obtain ⟨B', hB', hfit, hlt⟩ := this hB.2
  exact hlt (hmax B' (by simp [hB', hfit]))

lemma ff_key (S : List (List ℝ)) (a : ℝ) (j' : ℕ) (hj : j' < ffChoice S a) :
    1 < (S.getD j' []).sum + a := by
  have hlen : j' < S.length := lt_of_lt_of_le hj List.findIdx_le_length
  have := List.not_of_lt_findIdx hj
  rw [List.getD_eq_getElem _ _ hlen]
  simp at this
  linarith

lemma bf_key (S : List (List ℝ)) (a : ℝ) (hS : Half S)
    (hlev : (S.getD (bfChoice S a) []).sum ≤ 1 / 2) (j' : ℕ) (hj : j' < bfChoice S a) :
    1 < (S.getD j' []).sum + a := by
  have hlen : j' < S.length := lt_of_lt_of_le hj List.findIdx_le_length
  by_contra hcon
  push Not at hcon
  have hc : bfChoice S a < S.length := by
    rcases lt_or_eq_of_le (bf_good S a).1 with h | h
    · exact h
    · have := (bf_good S a).2 h j' hlen; linarith
  have hp : (S[bfChoice S a]'hc).sum + a ≤ 1 ∧
      ∀ B' ∈ S, B'.sum + a ≤ 1 → B'.sum ≤ (S[bfChoice S a]'hc).sum := by
    have := @List.findIdx_getElem (List ℝ)
      (fun B : List ℝ => decide (B.sum + a ≤ 1 ∧ ∀ B' ∈ S, B'.sum + a ≤ 1 → B'.sum ≤ B.sum)) S hc
    exact of_decide_eq_true this
  have h1 := hp.2 (S[j']) (List.getElem_mem hlen)
    (by rw [List.getD_eq_getElem _ _ hlen] at hcon; exact hcon)
  rw [List.getD_eq_getElem _ _ hc] at hlev
  have h2 := hS j' (bfChoice S a) hc hj
    (by rw [List.getD_eq_getElem _ _ hlen]; linarith)
  rw [List.getD_eq_getElem _ _ hc] at h2
  linarith

lemma foldr_max_lt (a : ℝ) (ha : 0 < a) :
    ∀ l : List ℝ, (∀ x ∈ l, x < a) → l.foldr max 0 < a := by
  intro l
  induction l with
  | nil => intro _; simpa using ha
  | cons x l ih =>
    intro h
    simp only [List.foldr_cons]
    exact max_lt (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

lemma general (ch : List (List ℝ) → ℝ → ℕ) (hg : GoodCh ch) (L : List ℝ)
    (hpos : ∀ a ∈ L, 0 < a) (i : Fin L.length)
    (hkey : ∀ j' < binOf ch L i, 1 < ((run ch (L.take i)).getD j' []).sum + L.get i) :
    coarseness (run ch L) (binOf ch L i) < L.get i := by
  have hai : 0 < L.get i := hpos _ (List.get_mem L i)
  set S := run ch (L.take i) with hSdef
  have hP : run ch L =
      (L.drop i).foldl (fun bins a => placeAt bins (ch bins a) a) S := by
    rw [hSdef]
    unfold run
    conv_lhs => rw [← List.take_append_drop (i : ℕ) L]
    rw [List.foldl_append]
  obtain ⟨hlenP, hmono⟩ := foldl_mono ch (L.drop i) S
    (fun a ha => (hpos a (List.mem_of_mem_drop ha)).le)
  have hcS : binOf ch L i ≤ S.length := (hg S (L.get i)).1
  unfold coarseness
  apply foldr_max_lt _ hai
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨B, hB, rfl⟩ := hx
  rw [List.mem_iff_getElem] at hB
  obtain ⟨t, ht, rfl⟩ := hB
  rw [List.length_take] at ht
  have htc : t < binOf ch L i := lt_of_lt_of_le ht (min_le_left _ _)
  have htS : t < S.length := lt_of_lt_of_le htc hcS
  have htP : t < (run ch L).length := lt_of_lt_of_le ht (min_le_right _ _)
  rw [List.getElem_take]
  have h1 := hkey t htc
  have h2 := hmono t htS
  rw [← hP, List.getD_eq_getElem _ _ htP] at h2
  linarith

end DA7E5FD9

open BinPacking.FirstFit in
theorem solution (L : List ℝ) (hL : IsList L) :
    (∀ i : Fin L.length, levelBefore ffChoice L i ≤ 1 / 2 →
        coarseness (ffPack L) (binOf ffChoice L i) < L.get i) ∧
    (∀ i : Fin L.length, levelBefore bfChoice L i ≤ 1 / 2 →
        coarseness (bfPack L) (binOf bfChoice L i) < L.get i) := by
  have hpos : ∀ a ∈ L, 0 < a := fun a ha => (hL a ha).1
  constructor
  · intro i _
    exact DA7E5FD9.general ffChoice DA7E5FD9.ff_good L hpos i
      (fun j' hj' => DA7E5FD9.ff_key _ _ j' hj')
  · intro i hi
    apply DA7E5FD9.general bfChoice DA7E5FD9.bf_good L hpos i
    intro j' hj'
    have hhalf : DA7E5FD9.Half (run bfChoice (L.take i)) :=
      DA7E5FD9.half_foldl bfChoice DA7E5FD9.bf_good (L.take i) []
        (fun a ha => hpos a (List.mem_of_mem_take ha)) DA7E5FD9.half_nil
    exact DA7E5FD9.bf_key _ _ hhalf hi j' hj'
