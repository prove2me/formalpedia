-- Prove2me | solution 1 for BinPacking.FirstFit.weight_ge_one_of_level_gt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:20:59.116375+00:00
-- url     : https://prove2.me/submissions/c929855c-1ea5-4ef8-8dbf-e750bd2315f6

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W

set_option autoImplicit false

namespace E47E202F
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


def Pos (S : List (List ℝ)) : Prop := ∀ j : ℕ, ∀ x ∈ S.getD j [], 0 < x

def Idx (S : List (List ℝ)) : Prop :=
  ∀ j : ℕ, j < S.length → ∀ k : ℕ, k < (S.getD j []).length →
    ((S.getD j []).take k).sum ≤ 1 / 2 → ∀ j' < j, 1 < (S.getD j' []).sum + (S.getD j []).getD k 0

lemma placeAt_getD_old (S : List (List ℝ)) (c : ℕ) (a : ℝ) (hc : c < S.length) (j : ℕ) :
    (placeAt S c a).getD j [] = if j = c then S.getD j [] ++ [a] else S.getD j [] := by
  unfold placeAt
  rw [if_pos hc]
  by_cases hj : j < S.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj]
    simp only [List.getElem_mapIdx]
  · rw [List.getD_eq_default _ _ (by simpa using hj), List.getD_eq_default _ _ (by omega)]
    have : j ≠ c := by omega
    simp [this]

lemma placeAt_getD_new (S : List (List ℝ)) (c : ℕ) (a : ℝ) (hc : ¬ c < S.length) (j : ℕ) :
    (placeAt S c a).getD j [] = if j = S.length then [a] else S.getD j [] := by
  rw [placeAt_new S c a hc]
  split_ifs with h
  · subst h; simp
  · by_cases hj : j < S.length
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
        List.getElem_append_left hj]
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma pos_step (ch : List (List ℝ) → ℝ → ℕ) (S : List (List ℝ)) (a : ℝ) (ha : 0 < a)
    (hS : Pos S) : Pos (placeAt S (ch S a) a) := by
  intro j x hx
  by_cases hc : ch S a < S.length
  · rw [placeAt_getD_old S _ a hc] at hx
    split_ifs at hx
    · rcases List.mem_append.mp hx with h | h
      · exact hS j x h
      · simp at h; rw [h]; exact ha
    · exact hS j x hx
  · rw [placeAt_getD_new S _ a hc] at hx
    split_ifs at hx
    · simp at hx; rw [hx]; exact ha
    · exact hS j x hx

lemma idx_step (ch : List (List ℝ) → ℝ → ℕ) (hg : GoodCh ch)
    (hkey : ∀ (S : List (List ℝ)) (a : ℝ), Half S → (S.getD (ch S a) []).sum ≤ 1 / 2 →
      ∀ j' < ch S a, 1 < (S.getD j' []).sum + a)
    (S : List (List ℝ)) (a : ℝ) (ha : 0 < a)
    (hH : Half S) (hS : Idx S) : Idx (placeAt S (ch S a) a) := by
  intro j hj k hk hpre j' hj'
  have hjS : j ≤ S.length := by
    by_cases hc : ch S a < S.length
    · rw [placeAt_len_eq S _ a hc] at hj; omega
    · rw [placeAt_new S _ a hc] at hj; simp at hj; omega
  have hj'S : j' < S.length := by omega
  have hmono := placeAt_mono S (ch S a) a ha.le j' hj'S
  have hcle := (hg S a).1
  by_cases hc : ch S a < S.length
  · rw [placeAt_getD_old S _ a hc j] at hk hpre ⊢
    split_ifs at hk hpre ⊢ with hjc
    · -- j = c
      simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
      · rw [List.take_append_of_le_length hk'.le] at hpre
        rw [List.getD_append _ _ _ _ hk']
        have := hS j (by omega) k hk' hpre j' hj'
        linarith
      · subst hk'
        rw [List.take_append_of_le_length le_rfl, List.take_length] at hpre
        rw [List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        subst hjc
        have := hkey S a hH hpre j' hj'
        linarith
    · have hjlt : j < S.length := by
        rw [placeAt_len_eq S _ a hc] at hj; exact hj
      have := hS j hjlt k hk hpre j' hj'
      linarith
  · have hcl : ch S a = S.length := le_antisymm hcle (not_lt.mp hc)
    rw [placeAt_getD_new S _ a hc j] at hk hpre ⊢
    split_ifs at hk hpre ⊢ with hjc
    · simp at hk
      subst hk
      simp only [List.getD_cons_zero]
      have h0 : (S.getD (ch S a) []).sum ≤ 1 / 2 := by
        rw [hcl, List.getD_eq_default _ _ le_rfl]; norm_num
      have := hkey S a hH h0 j' (by omega)
      linarith
    · have hjlt : j < S.length := by omega
      have := hS j hjlt k hk hpre j' hj'
      linarith

lemma inv_foldl (ch : List (List ℝ) → ℝ → ℕ) (hg : GoodCh ch)
    (hkey : ∀ (S : List (List ℝ)) (a : ℝ), Half S → (S.getD (ch S a) []).sum ≤ 1 / 2 →
      ∀ j' < ch S a, 1 < (S.getD j' []).sum + a) :
    ∀ (M : List ℝ) (S : List (List ℝ)), (∀ a ∈ M, 0 < a) → Half S → Pos S → Idx S →
      Pos (M.foldl (fun bins a => placeAt bins (ch bins a) a) S) ∧
      Idx (M.foldl (fun bins a => placeAt bins (ch bins a) a) S) := by
  intro M
  induction M with
  | nil => intro S _ _ hP hI; exact ⟨hP, hI⟩
  | cons b M ih =>
    intro S hM hH hP hI
    simp only [List.foldl_cons]
    have hb : 0 < b := hM b (by simp)
    exact ih _ (fun a ha => hM a (by simp [ha])) (half_step ch hg S b hb hH)
      (pos_step ch S b hb hP) (idx_step ch hg hkey S b hb hH hI)

lemma W_nonneg (z : ℝ) (hz : 0 < z) : 0 ≤ W z := by
  unfold W; split_ifs <;> linarith

lemma W_ge (z : ℝ) (hz : 0 < z) (hz2 : z ≤ 1 / 2) : 6 / 5 * z ≤ W z := by
  unfold W; split_ifs <;> linarith

lemma W_sum_ge : ∀ r : List ℝ, (∀ z ∈ r, 0 < z ∧ z ≤ 1 / 2) → 6 / 5 * r.sum ≤ (r.map W).sum := by
  intro r
  induction r with
  | nil => intro _; simp
  | cons z r ih =>
    intro h
    simp only [List.sum_cons, List.map_cons]
    have h1 := W_ge z (h z (by simp)).1 (h z (by simp)).2
    have h2 := ih (fun y hy => h y (by simp [hy]))
    linarith

lemma arith (B : List ℝ) (α : ℝ) (hα : α < 1 / 2) (hpos : ∀ x ∈ B, 0 < x)
    (hsum : 1 - α < B.sum)
    (hex : ∀ k < B.length, (B.take k).sum ≤ 1 / 2 → α < B.getD k 0) :
    1 ≤ (B.map W).sum := by
  by_cases hbig : ∃ b ∈ B, 1 / 2 < b
  · obtain ⟨b, hb, hb2⟩ := hbig
    have hWb : W b = 1 := by
      unfold W
      rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    have := List.single_le_sum (l := B.map W)
      (fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        exact W_nonneg z (hpos z hz)) (W b) (List.mem_map_of_mem hb)
    linarith
  · push Not at hbig
    match B, hpos, hsum, hex, hbig with
    | [], _, hsum, _, _ => simp at hsum; linarith
    | [x], _, hsum, _, hbig =>
      have := hbig x (by simp)
      simp at hsum; linarith
    | x :: y :: r, hpos, hsum, hex, hbig =>
      have hx := hex 0 (by simp) (by simp)
      have hy := hex 1 (by simp) (by simp; linarith [hbig x (by simp)])
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hx hy
      have hr := W_sum_ge r (fun z hz => ⟨hpos z (by simp [hz]), hbig z (by simp [hz])⟩)
      simp only [List.sum_cons] at hsum
      simp only [List.map_cons, List.sum_cons]
      have hx0 := hpos x (by simp)
      have hy0 := hpos y (by simp)
      have hx1 := hbig x (by simp)
      have hy1 := hbig y (by simp)
      have hr0 : 0 ≤ r.sum := List.sum_nonneg (fun z hz => (hpos z (by simp [hz])).le)
      generalize (r.map W).sum = R at hr ⊢
      unfold W
      split_ifs <;> linarith

lemma main (ch : List (List ℝ) → ℝ → ℕ) (hg : GoodCh ch)
    (hkey : ∀ (S : List (List ℝ)) (a : ℝ), Half S → (S.getD (ch S a) []).sum ≤ 1 / 2 →
      ∀ j' < ch S a, 1 < (S.getD j' []).sum + a)
    (L : List ℝ) (hL : IsList L) (j : ℕ) (hj : j < (run ch L).length)
    (hα : coarseness (run ch L) j < 1 / 2)
    (hsum : 1 - coarseness (run ch L) j < ((run ch L)[j]).sum) :
    1 ≤ (((run ch L)[j]).map W).sum := by
  have hpos : ∀ a ∈ L, 0 < a := fun a ha => (hL a ha).1
  obtain ⟨hP, hI⟩ := inv_foldl ch hg hkey L [] hpos half_nil
    (by intro j x hx; simp at hx) (by intro j hj; simp at hj)
  change Pos (run ch L) at hP
  change Idx (run ch L) at hI
  set P := run ch L with hPdef
  have hB : P[j] = P.getD j [] := (List.getD_eq_getElem _ _ hj).symm
  rw [hB] at hsum ⊢
  apply arith _ _ hα (fun x hx => hP j x hx) hsum
  intro k hk hpre
  have hkey2 := hI j hj k hk hpre
  set x := (P.getD j []).getD k 0
  have hxpos : 0 < x := hP j x (by
    simp only [x]; rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
  unfold coarseness
  apply foldr_max_lt _ hxpos
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨B, hB, rfl⟩ := hy
  rw [List.mem_iff_getElem] at hB
  obtain ⟨t, ht, rfl⟩ := hB
  rw [List.length_take] at ht
  have htj : t < j := lt_of_lt_of_le ht (min_le_left _ _)
  have htP : t < P.length := by omega
  rw [List.getElem_take]
  have := hkey2 t htj
  rw [List.getD_eq_getElem _ _ htP] at this
  linarith

end E47E202F

open BinPacking.FirstFit in
theorem solution (L : List ℝ) (hL : IsList L) :
    (∀ (j : ℕ) (hj : j < (ffPack L).length), coarseness (ffPack L) j < 1 / 2 →
        1 - coarseness (ffPack L) j < ((ffPack L)[j]).sum →
        1 ≤ (((ffPack L)[j]).map W).sum) ∧
    (∀ (j : ℕ) (hj : j < (bfPack L).length), coarseness (bfPack L) j < 1 / 2 →
        1 - coarseness (bfPack L) j < ((bfPack L)[j]).sum →
        1 ≤ (((bfPack L)[j]).map W).sum) := by
  constructor
  · intro j hj h1 h2
    exact E47E202F.main ffChoice E47E202F.ff_good
      (fun S a _ _ j' hj' => E47E202F.ff_key S a j' hj') L hL j hj h1 h2
  · intro j hj h1 h2
    exact E47E202F.main bfChoice E47E202F.bf_good
      (fun S a hH hlev j' hj' => E47E202F.bf_key S a hH hlev j' hj') L hL j hj h1 h2
