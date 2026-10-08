-- Prove2me | solution 1 for BinPacking.FirstFit.weight_deficit_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:05:17.506345+00:00
-- url     : https://prove2.me/submissions/e8610551-648f-4aaf-a2ec-6f38da56a4dc

import Mathlib
import Definitions.Def_BinPacking_FirstFit_Model
import Definitions.Def_BinPacking_FirstFit_W



namespace BinPacking.FirstFit

lemma wdb_W_nonneg (x : ℝ) (hx : 0 < x) : 0 ≤ W x := by
  unfold W; split_ifs <;> linarith

lemma wdb_W_ge (x : ℝ) (hx : 0 < x) (h2 : x ≤ 1/2) : 6/5 * x ≤ W x := by
  unfold W; split_ifs <;> linarith

lemma wdb_W_ge2 (x α : ℝ) (h1 : 1/6 < α) (h3 : α ≤ 1/3) (hx : α < x) (h2 : x ≤ 1/2) :
    6/5 * x + 3/5 * (α - 1/6) ≤ W x := by
  unfold W; split_ifs <;> linarith

lemma wdb_W_gt (x : ℝ) (hx : 1/3 < x) (h2 : x ≤ 1/2) : 1/2 < W x := by
  unfold W; split_ifs <;> linarith

lemma wdb_sum_nonneg (l : List ℝ) (h : ∀ x ∈ l, 0 < x) : 0 ≤ (l.map W).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := wdb_W_nonneg a (h a (by simp))
    have := ih (fun x hx => h x (by simp [hx]))
    linarith

lemma wdb_sum_ge (l : List ℝ) (h : ∀ x ∈ l, 0 < x ∧ x ≤ 1/2) : 6/5 * l.sum ≤ (l.map W).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have := wdb_W_ge a (h a (by simp)).1 (h a (by simp)).2
    have := ih (fun x hx => h x (by simp [hx]))
    linarith

lemma wdb_big (l : List ℝ) (h : ∀ x ∈ l, 0 < x ∧ x ≤ 1) (b : ℝ) (hb : b ∈ l) (hb2 : 1/2 < b) :
    1 ≤ (l.map W).sum := by
  induction l with
  | nil => simp at hb
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hb with rfl | hb'
    · have : W b = 1 := by unfold W; split_ifs <;> first | rfl | linarith
      have := wdb_sum_nonneg l (fun x hx => (h x (by simp [hx])).1)
      linarith
    · have := wdb_W_nonneg a (h a (by simp)).1
      have := ih (fun x hx => h x (by simp [hx])) hb'
      linarith

lemma wdb_arith (B : List ℝ) (hne : B ≠ []) (hpos : ∀ x ∈ B, 0 < x ∧ x ≤ 1) (α β : ℝ)
    (hα0 : 0 ≤ α) (hα : α < 1/2) (hβ : 0 < β) (hW : (B.map W).sum = 1 - β)
    (hc : α ≤ 1/6 ∨ ((∀ b rest, B = b :: rest → α < b) ∧
      (∀ b1 b2 rest, B = b1 :: b2 :: rest → b1 ≤ 1/2 → α < b2))) :
    (∃ b, B = [b] ∧ b ≤ 1/2) ∨ B.sum ≤ 1 - α - 5/9 * β := by
  have hhalf : ∀ x ∈ B, 0 < x ∧ x ≤ 1/2 := by
    intro x hx
    refine ⟨(hpos x hx).1, ?_⟩
    by_contra hcon
    have := wdb_big B hpos x hx (by linarith)
    linarith
  rcases hc with hc | ⟨h1, h2⟩
  · right
    have := wdb_sum_ge B hhalf
    linarith
  · obtain ⟨b1, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    rcases rest with _ | ⟨b2, rest⟩
    · left; exact ⟨b1, rfl, (hhalf b1 (by simp)).2⟩
    · right
      have hb1 := h1 b1 _ rfl
      have hb1h := hhalf b1 (by simp)
      have hb2h := hhalf b2 (by simp)
      have hb2 := h2 b1 b2 rest rfl hb1h.2
      have hr := wdb_sum_ge rest (fun x hx => hhalf x (by simp [hx]))
      simp only [List.map_cons, List.sum_cons] at hW ⊢
      by_cases hα3 : α ≤ 1/3
      · by_cases hα6 : α ≤ 1/6
        · have := wdb_W_ge b1 hb1h.1 hb1h.2
          have := wdb_W_ge b2 hb2h.1 hb2h.2
          linarith
        · push_neg at hα6
          have := wdb_W_ge2 b1 α hα6 hα3 hb1 hb1h.2
          have := wdb_W_ge2 b2 α hα6 hα3 hb2 hb2h.2
          linarith
      · push_neg at hα3
        have := wdb_W_gt b1 (by linarith) hb1h.2
        have := wdb_W_gt b2 (by linarith) hb2h.2
        have := wdb_sum_nonneg rest (fun x hx => (hhalf x (by simp [hx])).1)
        linarith

lemma wdb_placeAt_length (P : List (List ℝ)) (c : ℕ) (a : ℝ) :
    (placeAt P c a).length = if c < P.length then P.length else P.length + 1 := by
  unfold placeAt; split_ifs <;> simp

lemma wdb_placeAt_getD (P : List (List ℝ)) (c : ℕ) (a : ℝ) (i : ℕ) :
    (placeAt P c a).getD i [] = if c < P.length then (if i = c then P.getD i [] ++ [a] else P.getD i [])
      else (if i = P.length then [a] else P.getD i []) := by
  unfold placeAt
  split_ifs with h1 h2 h3
  · subst h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_getElem h1]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
    rcases (P[i]?) with _ | B <;> simp [h2]
  · subst h3
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  · simp only [List.getD_eq_getElem?_getD]
    rcases lt_or_gt_of_ne h3 with h | h
    · rw [List.getElem?_append_left h]
    · rw [List.getElem?_append_right (by omega)]
      have hn : P[i]? = none := List.getElem?_eq_none (by omega)
      obtain ⟨k, hk⟩ : ∃ k, i - P.length = k + 1 := ⟨i - P.length - 1, by omega⟩
      rw [hk, hn]; simp


def WGood (choose : List (List ℝ) → ℝ → ℕ) : Prop :=
  ∀ (P : List (List ℝ)) (a : ℝ), choose P a ≤ P.length ∧
    ∀ j', j' < choose P a → j' < P.length → (P.getD j' []).sum + a ≤ 1 →
      choose P a < P.length ∧ (P.getD j' []).sum ≤ (P.getD (choose P a) []).sum

def WInv (P : List (List ℝ)) : Prop :=
  (∀ i < P.length, P.getD i [] ≠ []) ∧ (∀ i, ∀ x ∈ P.getD i [], 0 < x ∧ x ≤ 1) ∧
  (∀ j' j, j' < j → j < P.length → ∀ b rest, P.getD j [] = b :: rest →
      1 - (P.getD j' []).sum < b) ∧
  (∀ j' j, j' < j → j < P.length → ∀ b1 b2 rest, P.getD j [] = b1 :: b2 :: rest → b1 ≤ 1/2 →
      1 - (P.getD j' []).sum < b2)

lemma wdb_step (P : List (List ℝ)) (c : ℕ) (a : ℝ) (ha : 0 < a ∧ a ≤ 1) (hI : WInv P)
    (hc : c ≤ P.length)
    (hg : ∀ j', j' < c → j' < P.length → (P.getD j' []).sum + a ≤ 1 →
      c < P.length ∧ (P.getD j' []).sum ≤ (P.getD c []).sum) :
    WInv (placeAt P c a) := by
  obtain ⟨hne, hpos, h1, h2⟩ := hI
  have hF := wdb_placeAt_getD P c a
  have hL := wdb_placeAt_length P c a
  have hgetD_out : ∀ i, P.length ≤ i → P.getD i [] = [] := by
    intro i hi; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  by_cases hcl : c < P.length
  · simp only [hcl, if_true] at hF hL
    have hmono : ∀ i, (P.getD i []).sum ≤ ((placeAt P c a).getD i []).sum := by
      intro i; rw [hF]; split_ifs <;> simp; linarith
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi; rw [hF]; split_ifs <;> simp_all
    · intro i x hx; rw [hF] at hx; split_ifs at hx
      · simp at hx; rcases hx with hx | rfl
        · exact hpos i x hx
        · exact ha
      · exact hpos i x hx
    · intro j' j hjj hj b rest hb
      rw [hL] at hj
      have := h1 j' j hjj hj
      have hm := hmono j'
      rw [hF] at hb
      split_ifs at hb
      · obtain ⟨x, r, hxr⟩ := List.exists_cons_of_ne_nil (hne j hj)
        rw [hxr] at hb; simp at hb
        have := this x r hxr; rw [← hb.1]; linarith
      · have := this b rest hb; linarith
    · intro j' j hjj hj b1 b2 rest hb hb1
      rw [hL] at hj
      have hm := hmono j'
      rw [hF] at hb
      split_ifs at hb with hjc
      · obtain ⟨x, r, hxr⟩ := List.exists_cons_of_ne_nil (hne j hj)
        rw [hxr] at hb
        rcases r with _ | ⟨y, r'⟩
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hb
          obtain ⟨hx1, hx2, -⟩ := hb
          rw [← hx1] at hb1; rw [← hx2]
          have hj'c : j' ≠ c := by omega
          have hQj' : (placeAt P c a).getD j' [] = P.getD j' [] := by rw [hF]; simp [hj'c]
          rw [hQj']
          by_contra hcon
          push_neg at hcon
          have hfit := hg j' (by omega) (by omega) (by linarith)
          have := h1 j' j hjj hj x [] hxr
          have hf2 := hfit.2
          rw [← hjc, hxr] at hf2
          simp only [List.sum_cons, List.sum_nil, add_zero] at hf2
          linarith
        · simp only [List.cons_append, List.cons.injEq] at hb
          obtain ⟨hx1, hx2, -⟩ := hb
          rw [← hx1] at hb1; rw [← hx2]
          have := h2 j' j hjj hj x y r' hxr hb1
          linarith
      · have := h2 j' j hjj hj b1 b2 rest hb hb1; linarith
  · have hceq : c = P.length := by omega
    simp only [hcl, if_false] at hF hL
    have hsame : ∀ i, i < P.length → (placeAt P c a).getD i [] = P.getD i [] := by
      intro i hi; rw [hF]; simp [show i ≠ P.length by omega]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi; rw [hF]; split_ifs with h
      · simp
      · exact hne i (by rw [hL] at hi; omega)
    · intro i x hx; rw [hF] at hx; split_ifs at hx
      · simp at hx; rw [hx]; exact ha
      · exact hpos i x hx
    · intro j' j hjj hj b rest hb
      rw [hL] at hj
      rw [hsame j' (by omega)]
      by_cases hjl : j < P.length
      · rw [hsame j hjl] at hb; exact h1 j' j hjj hjl b rest hb
      · have hjeq : j = P.length := by omega
        rw [hF] at hb; simp [hjeq] at hb
        obtain ⟨rfl, -⟩ := hb
        by_contra hcon; push_neg at hcon
        have := hg j' (by omega) (by omega) (by linarith)
        omega
    · intro j' j hjj hj b1 b2 rest hb hb1
      rw [hL] at hj
      rw [hsame j' (by omega)]
      by_cases hjl : j < P.length
      · rw [hsame j hjl] at hb; exact h2 j' j hjj hjl b1 b2 rest hb hb1
      · have hjeq : j = P.length := by omega
        rw [hF] at hb; simp [hjeq] at hb

lemma wdb_run (choose : List (List ℝ) → ℝ → ℕ) (hG : WGood choose) (L : List ℝ) (hL : IsList L) :
    WInv (run choose L) := by
  induction L using List.reverseRecOn with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [run]
  | append_singleton L a ih =>
    have hL' : IsList L := fun x hx => hL x (by simp [hx])
    have : run choose (L ++ [a]) = placeAt (run choose L) (choose (run choose L) a) a := by
      simp [run, List.foldl_append]
    rw [this]
    exact wdb_step _ _ a (hL a (by simp)) (ih hL') (hG _ a).1 (hG _ a).2


lemma wdb_ff_good : WGood ffChoice := by
  intro P a
  refine ⟨List.findIdx_le_length, ?_⟩
  intro j' hj' hj'l hfit
  exfalso
  have := List.not_of_lt_findIdx hj'
  rw [List.getD_eq_getElem _ _ hj'l] at hfit
  simp [hfit] at this

lemma wdb_bf_good : WGood bfChoice := by
  classical
  intro P a
  refine ⟨List.findIdx_le_length, ?_⟩
  intro j' hj' hj'l hfit
  rw [List.getD_eq_getElem _ _ hj'l] at hfit ⊢
  obtain ⟨Bm, hBm, hmax⟩ := Finset.exists_max_image
    (P.toFinset.filter (fun B => B.sum + a ≤ 1)) (fun B => B.sum)
    ⟨P[j'], by simp [hfit]⟩
  simp only [Finset.mem_filter, List.mem_toFinset] at hBm hmax
  have hlt : bfChoice P a < P.length := by
    unfold bfChoice
    apply List.findIdx_lt_length_of_exists
    refine ⟨Bm, hBm.1, ?_⟩
    simp only [decide_eq_true_eq]
    exact ⟨hBm.2, fun B' hB' hf => hmax B' ⟨hB', hf⟩⟩
  refine ⟨hlt, ?_⟩
  rw [List.getD_eq_getElem _ _ hlt]
  unfold bfChoice at hlt ⊢
  have := List.findIdx_getElem (w := hlt)
  simp only [decide_eq_true_eq] at this
  exact this.2 _ (List.getElem_mem _) hfit

lemma wdb_foldr (l : List ℝ) : 0 ≤ l.foldr max 0 ∧ (l.foldr max 0 = 0 ∨ l.foldr max 0 ∈ l) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    refine ⟨le_max_of_le_right ih.1, ?_⟩
    rcases le_total x (l.foldr max 0) with h | h
    · rw [max_eq_right h]
      rcases ih.2 with h' | h'
      · left; exact h'
      · right; right; exact h'
    · rw [max_eq_left h]; right; left; rfl

lemma wdb_coarse (P : List (List ℝ)) (j : ℕ) : 0 ≤ coarseness P j ∧ (coarseness P j = 0 ∨
    ∃ j', j' < j ∧ j' < P.length ∧ coarseness P j = 1 - (P.getD j' []).sum) := by
  unfold coarseness
  obtain ⟨h0, h⟩ := wdb_foldr ((P.take j).map (fun B => 1 - B.sum))
  refine ⟨h0, ?_⟩
  rcases h with h | h
  · left; exact h
  · right
    obtain ⟨B, hB, hBv⟩ := List.mem_map.1 h
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hB
    simp only [List.length_take] at hk
    refine ⟨k, by omega, by omega, ?_⟩
    rw [← hBv, List.getElem_take, List.getD_eq_getElem _ _ (by omega)]

lemma wdb_core (choose : List (List ℝ) → ℝ → ℕ) (hG : WGood choose) (L : List ℝ) (hL : IsList L)
    (j : ℕ) (hj : j < (run choose L).length) (β : ℝ) (hα : coarseness (run choose L) j < 1 / 2)
    (hβ : 0 < β) (hW : (((run choose L)[j]).map W).sum = 1 - β) :
    (∃ b : ℝ, (run choose L)[j] = [b] ∧ b ≤ 1 / 2) ∨
      ((run choose L)[j]).sum ≤ 1 - coarseness (run choose L) j - 5 / 9 * β := by
  obtain ⟨hne, hpos, h1, h2⟩ := wdb_run choose hG L hL
  rw [← List.getD_eq_getElem _ [] hj] at hW ⊢
  obtain ⟨hc0, hc⟩ := wdb_coarse (run choose L) j
  apply wdb_arith _ (hne j hj) (hpos j) _ β hc0 hα hβ hW
  by_cases h6 : coarseness (run choose L) j ≤ 1/6
  · left; exact h6
  · right
    rcases hc with hc | ⟨j', hj'j, hj'l, hcv⟩
    · exfalso; rw [hc] at h6; norm_num at h6
    · rw [hcv]
      exact ⟨fun b rest hb => h1 j' j hj'j hj b rest hb,
        fun b1 b2 rest hb hb1 => h2 j' j hj'j hj b1 b2 rest hb hb1⟩

theorem wdb_main (L : List ℝ) (hL : IsList L) :
    (∀ (j : ℕ) (hj : j < (ffPack L).length) (β : ℝ), coarseness (ffPack L) j < 1 / 2 →
        0 < β → (((ffPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (ffPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((ffPack L)[j]).sum ≤ 1 - coarseness (ffPack L) j - 5 / 9 * β) ∧
    (∀ (j : ℕ) (hj : j < (bfPack L).length) (β : ℝ), coarseness (bfPack L) j < 1 / 2 →
        0 < β → (((bfPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (bfPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((bfPack L)[j]).sum ≤ 1 - coarseness (bfPack L) j - 5 / 9 * β) :=
  ⟨fun j hj β h1 h2 h3 => wdb_core ffChoice wdb_ff_good L hL j hj β h1 h2 h3,
   fun j hj β h1 h2 h3 => wdb_core bfChoice wdb_bf_good L hL j hj β h1 h2 h3⟩

end BinPacking.FirstFit

open BinPacking.FirstFit


theorem solution (L : List ℝ) (hL : IsList L) :
    (∀ (j : ℕ) (hj : j < (ffPack L).length) (β : ℝ), coarseness (ffPack L) j < 1 / 2 →
        0 < β → (((ffPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (ffPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((ffPack L)[j]).sum ≤ 1 - coarseness (ffPack L) j - 5 / 9 * β) ∧
    (∀ (j : ℕ) (hj : j < (bfPack L).length) (β : ℝ), coarseness (bfPack L) j < 1 / 2 →
        0 < β → (((bfPack L)[j]).map W).sum = 1 - β →
        (∃ b : ℝ, (bfPack L)[j] = [b] ∧ b ≤ 1 / 2) ∨
          ((bfPack L)[j]).sum ≤ 1 - coarseness (bfPack L) j - 5 / 9 * β) := by
  exact wdb_main L hL
