-- Prove2me | solution 1 for BinPacking.Decreasing.ffd_position_order
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T08:02:12.323154+00:00
-- url     : https://prove2.me/submissions/802acb61-022f-41a5-9a33-d5587bc40c1a

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model



namespace BinPacking.Decreasing

lemma po_sorted (L : List ℝ) : (sortDesc L).Pairwise (fun a b => decide (b ≤ a)) := by
  unfold sortDesc
  apply List.pairwise_mergeSort
  · intro a b c h1 h2; simp at *; linarith
  · intro a b; simp; exact le_total _ _

lemma po_filter (l : List ℝ) (hs : l.Pairwise (fun a b => decide (b ≤ a))) :
    ∀ (k : ℕ) (hk : k < l.length), (1/3 : ℝ) < l[k] →
      k < (l.filter (fun a => decide ((1 / 3 : ℝ) < a))).length := by
  induction l with
  | nil => intro k hk; simp at hk
  | cons x t ih =>
    intro k hk hx
    rw [List.pairwise_cons] at hs
    cases k with
    | zero =>
      simp at hx; simp [List.filter_cons, hx]
    | succ k =>
      simp at hx hk
      have hxt : t[k] ≤ x := by simpa using hs.1 t[k] (List.getElem_mem _)
      have : (1/3:ℝ) < x := by linarith
      rw [List.filter_cons, if_pos (by simpa using this), List.length_cons]
      exact Nat.succ_lt_succ (ih hs.2 k hk (by rw [one_div]; exact hx))

lemma po_run_succ (c : List (List ℝ) → ℝ → ℕ) (S : List ℝ) (n : ℕ) (hn : n < S.length) :
    run c (S.take (n+1)) = placeAt (run c (S.take n)) (c (run c (S.take n)) S[n]) S[n] := by
  unfold run
  rw [List.take_add_one, List.getElem?_eq_getElem hn, List.foldl_append]
  simp

lemma po_place_getD (bins : List (List ℝ)) (j b : ℕ) (a : ℝ) :
    (placeAt bins j a).getD b [] =
      if j < bins.length then (if b = j then bins.getD b [] ++ [a] else bins.getD b [])
      else (if b = bins.length then [a] else bins.getD b []) := by
  unfold placeAt
  split_ifs with h1 h2 h3
  · subst h2
    simp [List.getD_eq_getElem?_getD, h1]
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
    cases bins[b]? <;> simp [h2]
  · subst h3
    simp [List.getD_eq_getElem?_getD]
  · simp only [List.getD_eq_getElem?_getD]
    rcases lt_or_gt_of_ne h3 with h | h
    · rw [List.getElem?_append_left (by simpa using h)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma po_place_prefix (bins : List (List ℝ)) (j b : ℕ) (a : ℝ) :
    bins.getD b [] <+: (placeAt bins j a).getD b [] := by
  rw [po_place_getD]
  split_ifs with h1 h2 h3
  · exact List.prefix_append _ _
  · exact List.prefix_refl _
  · subst h3; simp [List.getD_eq_getElem?_getD]
  · exact List.prefix_refl _

lemma po_place_self (bins : List (List ℝ)) (j : ℕ) (a : ℝ) (hj : j ≤ bins.length) :
    (placeAt bins j a).getD j [] = bins.getD j [] ++ [a] := by
  rw [po_place_getD]
  by_cases h1 : j < bins.length
  · simp [h1]
  · have : j = bins.length := by omega
    subst this; simp [List.getD_eq_getElem?_getD]

lemma po_prefix_mono (c : List (List ℝ) → ℝ → ℕ) (S : List ℝ) (b n m : ℕ) (hnm : n ≤ m) :
    (run c (S.take n)).getD b [] <+: (run c (S.take m)).getD b [] := by
  induction m, hnm using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ m _ ih =>
    refine ih.trans ?_
    by_cases hm : m < S.length
    · rw [po_run_succ c S m hm]; exact po_place_prefix _ _ _ _
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]

lemma po_ff_le (bins : List (List ℝ)) (a : ℝ) : ffChoice bins a ≤ bins.length :=
  List.findIdx_le_length

lemma po_inv (S : List ℝ) (hS : ∀ a ∈ S, (1/6 : ℝ) ≤ a ∧ a ≤ 1) (n : ℕ) :
    ∀ b, ((run ffChoice (S.take n)).getD b []).sum ≤ 1 ∧
      ∀ x ∈ (run ffChoice (S.take n)).getD b [], (1/6 : ℝ) ≤ x := by
  induction n with
  | zero => intro b; simp [run, List.getD_eq_getElem?_getD]
  | succ n ih =>
    by_cases hn : n < S.length
    · intro b
      rw [po_run_succ _ S n hn, po_place_getD]
      have ha := hS S[n] (List.getElem_mem _)
      set bins := run ffChoice (S.take n)
      split_ifs with h1 h2 h3
      · subst h2
        have hp : bins[ffChoice bins S[n]].sum + S[n] ≤ 1 := by
          have := List.findIdx_getElem (w := h1)
          simp only [decide_eq_true_eq] at this
          exact this
        have e : bins.getD (ffChoice bins S[n]) [] = bins[ffChoice bins S[n]] := by
          simp [List.getD_eq_getElem?_getD, h1]
        refine ⟨?_, ?_⟩
        · rw [List.sum_append, e]; simpa using hp
        · intro x hx
          rw [List.mem_append] at hx
          rcases hx with hx | hx
          · exact (ih _).2 x hx
          · simp at hx; rw [hx]; exact ha.1
      · exact ih b
      · simp; exact ⟨ha.2, by linarith [ha.1]⟩
      · exact ih b
    · rw [List.take_of_length_le (by omega)]
      rw [List.take_of_length_le (by omega)] at ih
      exact ih

lemma po_sum_ge (l : List ℝ) (h : ∀ x ∈ l, (1/6 : ℝ) ≤ x) : 0 ≤ l.sum :=
  List.sum_nonneg (fun x hx => by have := h x hx; linarith)

theorem po_core2 (S : List ℝ) (hsorted : S.Pairwise (fun a b => decide (b ≤ a)))
    (hS : ∀ a ∈ S, (1/6 : ℝ) ≤ a ∧ a ≤ 1) (i i' : Fin S.length)
    (hi' : (S.filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i' : ℕ))
    (hk : slotOf ffChoice S i + 1 <
      ((run ffChoice S).getD (binOf ffChoice S i) []).length)
    (hle : binOf ffChoice S i < binOf ffChoice S i' ∨
      (binOf ffChoice S i = binOf ffChoice S i' ∧
        slotOf ffChoice S i ≤ slotOf ffChoice S i')) :
    i ≤ i' := by
  have ha' : S[(i' : ℕ)] ≤ 1/3 := by
    by_contra hc
    push_neg at hc
    have := po_filter S hsorted i' i'.2 hc
    omega
  by_contra hlt
  push_neg at hlt
  -- i' < i
  set G : ℕ → ℕ → List ℝ := fun n b => (run ffChoice (S.take n)).getD b [] with hG
  have hpre : ∀ b n m, n ≤ m → G n b <+: G m b := fun b n m h => po_prefix_mono _ S b n m h
  have hself : ∀ k : Fin S.length,
      G (k+1) (binOf ffChoice S k) = G k (binOf ffChoice S k) ++ [S[(k:ℕ)]] := by
    intro k
    simp only [hG, binOf]
    rw [po_run_succ _ S k k.2]
    exact po_place_self _ _ _ (po_ff_le _ _)
  have hslot : ∀ k : Fin S.length, slotOf ffChoice S k = (G k (binOf ffChoice S k)).length := by
    intro k; rfl
  rcases hle with hlt2 | ⟨heq, hsl⟩
  · -- different bins
    set j := binOf ffChoice S i
    set j' := binOf ffChoice S i'
    have hj' : j' = ffChoice (run ffChoice (S.take i')) S[(i':ℕ)] := rfl
    have hlen : j' ≤ (run ffChoice (S.take i')).length := po_ff_le _ _
    have hnot := List.not_of_lt_findIdx (p := fun B => decide (B.sum + S[(i':ℕ)] ≤ 1))
      (xs := run ffChoice (S.take i')) (i := j) (by rw [← ffChoice]; omega)
    simp only [decide_eq_false_iff_not, not_le] at hnot
    have e : G i' j = (run ffChoice (S.take i'))[j]'(by omega) := by
      simp [hG, List.getD_eq_getElem?_getD, show j < (run ffChoice (S.take i')).length by omega]
    rw [← e] at hnot
    -- B
    have hinvN : (G S.length j).sum ≤ 1 ∧ ∀ x ∈ G S.length j, (1/6:ℝ) ≤ x := po_inv S hS S.length j
    have hrunN : run ffChoice S = run ffChoice (S.take S.length) := by rw [List.take_length]
    rw [hrunN] at hk
    obtain ⟨C, hC⟩ := hpre j i' i hlt.le
    obtain ⟨D, hD⟩ := hpre j (i+1) S.length (by omega)
    rw [hself i] at hD
    change G i j ++ [S[(i:ℕ)]] ++ D = G S.length j at hD
    have hk' : (G i j).length + 1 < (G S.length j).length := by
      rw [hslot i] at hk; exact hk
    rw [← hD] at hk' hinvN
    simp at hk'
    obtain ⟨d, D', rfl⟩ : ∃ d D', D = d :: D' := by
      cases D with
      | nil => simp at hk'
      | cons d D' => exact ⟨d, D', rfl⟩
    rw [← hC] at hinvN
    obtain ⟨hsum, hmem⟩ := hinvN
    simp only [List.sum_append, List.sum_cons, List.sum_nil, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false] at hsum hmem
    have hd := hmem d (Or.inr (Or.inl rfl))
    have hai := hmem S[(i:ℕ)] (Or.inl (Or.inr rfl))
    have hCs := po_sum_ge C (fun x hx => hmem x (Or.inl (Or.inl (Or.inr hx))))
    have hDs := po_sum_ge D' (fun x hx => hmem x (Or.inr (Or.inr hx)))
    linarith
  · -- same bin
    set j := binOf ffChoice S i
    have h1 := hpre j (i'+1) i (by omega)
    rw [heq, hself i'] at h1
    have := h1.length_le
    have hsl' : (G i (binOf ffChoice S i')).length ≤ (G i' (binOf ffChoice S i')).length := by
      rw [hslot i, hslot i'] at hsl
      rwa [show binOf ffChoice S i = binOf ffChoice S i' from heq] at hsl
    simp at this
    omega

theorem po_core (L : List ℝ) (hL : IsList L)
    (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) (i i' : Fin (sortDesc L).length)
    (hi : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i : ℕ))
    (hi' : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i' : ℕ))
    (hk : slotOf ffChoice (sortDesc L) i + 1 <
      ((run ffChoice (sortDesc L)).getD (binOf ffChoice (sortDesc L) i) []).length)
    (hle : binOf ffChoice (sortDesc L) i < binOf ffChoice (sortDesc L) i' ∨
      (binOf ffChoice (sortDesc L) i = binOf ffChoice (sortDesc L) i' ∧
        slotOf ffChoice (sortDesc L) i ≤ slotOf ffChoice (sortDesc L) i')) :
    i ≤ i' := by
  refine po_core2 (sortDesc L) (po_sorted L) ?_ i i' hi' hk hle
  intro a ha
  rw [sortDesc, List.mem_mergeSort] at ha
  exact ⟨h6 a ha, (hL a ha).2⟩

end BinPacking.Decreasing

open BinPacking.Decreasing


theorem solution (L : List ℝ) (hL : IsList L)
    (h6 : ∀ a ∈ L, (1 / 6 : ℝ) ≤ a) (i i' : Fin (sortDesc L).length)
    (hi : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i : ℕ))
    (hi' : ((sortDesc L).filter (fun a => decide ((1 / 3 : ℝ) < a))).length ≤ (i' : ℕ))
    (hk : slotOf ffChoice (sortDesc L) i + 1 <
      ((run ffChoice (sortDesc L)).getD (binOf ffChoice (sortDesc L) i) []).length)
    (hle : binOf ffChoice (sortDesc L) i < binOf ffChoice (sortDesc L) i' ∨
      (binOf ffChoice (sortDesc L) i = binOf ffChoice (sortDesc L) i' ∧
        slotOf ffChoice (sortDesc L) i ≤ slotOf ffChoice (sortDesc L) i')) :
    i ≤ i' := by
  exact po_core L hL h6 i i' hi hi' hk hle
