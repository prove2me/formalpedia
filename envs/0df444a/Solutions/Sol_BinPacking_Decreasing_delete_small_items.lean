-- Prove2me | solution 1 for BinPacking.Decreasing.delete_small_items
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T13:22:15.481041+00:00
-- url     : https://prove2.me/submissions/52fd7782-1f97-4886-b410-63ab6caec586

import Mathlib
import Definitions.Def_BinPacking_Decreasing_Model

set_option autoImplicit false

namespace DSAux_7337ec4c
open BinPacking.Decreasing

lemma getD_lt {α : Type} (P : List α) (j : ℕ) (d : α) (hj : j < P.length) : P.getD j d = P[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl

lemma getD_ge {α : Type} (P : List α) (j : ℕ) (d : α) (hj : P.length ≤ j) : P.getD j d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]; rfl

lemma placeAt_lt {P : List (List ℝ)} {c : ℕ} {y : ℝ} (hc : c < P.length) :
    (placeAt P c y).length = P.length ∧
    ∀ j, (placeAt P c y).getD j [] = if j = c then P.getD j [] ++ [y] else P.getD j [] := by
  refine ⟨by simp [placeAt, hc], fun j => ?_⟩
  simp only [placeAt, hc, if_true]
  rcases lt_or_ge j P.length with hj | hj
  · rw [getD_lt _ _ _ (by simpa using hj), getD_lt _ _ _ hj, List.getElem_mapIdx]
  · rw [getD_ge _ _ _ (by simpa using hj), getD_ge _ _ _ hj]
    have : j ≠ c := by omega
    simp [this]

lemma placeAt_eq {P : List (List ℝ)} {y : ℝ} :
    placeAt P P.length y = P ++ [[y]] := by simp [placeAt]

lemma getD_app_lt (P : List (List ℝ)) (y : ℝ) (j : ℕ) (hj : j < P.length) :
    (P ++ [[y]]).getD j [] = P.getD j [] := by
  rw [getD_lt _ _ _ (by simp; omega), getD_lt _ _ _ hj, List.getElem_append_left hj]

lemma getD_app_eq (P : List (List ℝ)) (y : ℝ) :
    (P ++ [[y]]).getD P.length [] = [y] := by
  rw [getD_lt _ _ _ (by simp)]
  simp

lemma sum_placeAt (P : List (List ℝ)) (c : ℕ) (y : ℝ) (hc : c ≤ P.length) (f : ℕ → ℝ → ℝ) :
    ∑ j ∈ Finset.range (placeAt P c y).length, (((placeAt P c y).getD j []).map (f j)).sum =
      ∑ j ∈ Finset.range P.length, ((P.getD j []).map (f j)).sum + f c y := by
  rcases lt_or_eq_of_le hc with hc | rfl
  · obtain ⟨hl, hg⟩ := placeAt_lt (y := y) hc
    rw [hl]
    have : ∀ j ∈ Finset.range P.length, (((placeAt P c y).getD j []).map (f j)).sum =
        ((P.getD j []).map (f j)).sum + (if j = c then f j y else 0) := by
      intro j _
      rw [hg j]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [hc]
  · rw [placeAt_eq]
    simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_app_lt _ _ _ hj]
    · rw [getD_app_eq]
      simp

/-- the two properties of a placement rule that the argument uses -/
def GoodChoice (ch : List (List ℝ) → ℝ → ℕ) : Prop :=
  (∀ P a, ch P a ≤ P.length) ∧ (∀ P a, ch P a = P.length → ∀ B ∈ P, 1 < B.sum + a)

lemma ff_good : GoodChoice ffChoice := by
  refine ⟨fun P a => by unfold ffChoice; exact List.findIdx_le_length, fun P a h => ?_⟩
  unfold ffChoice at h
  have := List.findIdx_eq_length.mp h
  intro B hB
  have h2 := this B hB
  simp at h2
  linarith

lemma bf_good : GoodChoice bfChoice := by
  refine ⟨fun P a => by unfold bfChoice; exact List.findIdx_le_length, fun P a h => ?_⟩
  unfold bfChoice at h
  have hall := List.findIdx_eq_length.mp h
  intro B hB
  by_contra hcon'
  have hcon : B.sum + a ≤ 1 := not_lt.mp hcon'
  set s := P.toFinset.filter (fun B : List ℝ => B.sum + a ≤ 1) with hs
  have hne : s.Nonempty := ⟨B, by simp [hs, hB, hcon]⟩
  obtain ⟨B0, hB0, hmax⟩ := Finset.exists_max_image s (fun B : List ℝ => B.sum) hne
  simp only [hs, Finset.mem_filter, List.mem_toFinset] at hB0
  have := hall B0 hB0.1
  simp only [decide_eq_false_iff_not, not_and, not_forall] at this
  obtain ⟨B', hB', hfit, hlt⟩ := this hB0.2
  exact hlt (hmax B' (by simp [hs, hB', hfit]))

/-- total content of a list of bins -/
noncomputable def tot (P : List (List ℝ)) : ℝ :=
  ∑ j ∈ Finset.range P.length, ((P.getD j []).map (fun x : ℝ => x)).sum

lemma tot_placeAt (P : List (List ℝ)) (c : ℕ) (a : ℝ) (hc : c ≤ P.length) :
    tot (placeAt P c a) = tot P + a :=
  sum_placeAt P c a hc (fun _ x => x)

noncomputable def step (ch : List (List ℝ) → ℝ → ℕ) (bins : List (List ℝ)) (a : ℝ) :
    List (List ℝ) :=
  placeAt bins (ch bins a) a

lemma tot_fold (ch : List (List ℝ) → ℝ → ℕ) (hch : GoodChoice ch) : ∀ (B : List ℝ) (P : List (List ℝ)),
    tot (B.foldl (step ch) P) = tot P + B.sum
  | [], P => by simp
  | a :: B, P => by
    rw [List.foldl_cons, tot_fold ch hch B, step, tot_placeAt _ _ _ (hch.1 _ _), List.sum_cons]
    ring

lemma tot_ge (r : ℝ) (P : List (List ℝ)) (hP : ∀ B ∈ P, 1 < r * B.sum) :
    (P.length : ℝ) ≤ r * tot P := by
  unfold tot
  rw [Finset.mul_sum]
  calc (P.length : ℝ) = ∑ _j ∈ Finset.range P.length, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      rw [getD_lt _ _ _ hj, List.map_id']
      exact (hP _ (List.getElem_mem hj)).le

lemma small_phase (ch : List (List ℝ) → ℝ → ℕ) (hch : GoodChoice ch)
    (r : ℝ) (hr : 0 < r) (n0 : ℕ) : ∀ (B : List ℝ) (P : List (List ℝ)),
    (∀ a ∈ B, 0 < a ∧ r * a ≤ r - 1) →
    (P.length = n0 ∨ (P.length : ℝ) - 1 < r * tot P) →
    ((B.foldl (step ch) P).length = n0 ∨
      ((B.foldl (step ch) P).length : ℝ) - 1 < r * tot (B.foldl (step ch) P))
  | [], P, _, hP => by simpa using hP
  | a :: B, P, hB, hP => by
    rw [List.foldl_cons]
    apply small_phase ch hch r hr n0 B
    · exact fun x hx => hB x (List.mem_cons_of_mem _ hx)
    · obtain ⟨ha0, ha1⟩ := hB a List.mem_cons_self
      have htot : tot (step ch P a) = tot P + a := tot_placeAt _ _ _ (hch.1 _ _)
      rcases lt_or_eq_of_le (hch.1 P a) with hc | hc
      · have hl : (step ch P a).length = P.length := (placeAt_lt (y := a) hc).1
        rw [hl, htot]
        rcases hP with hP | hP
        · exact Or.inl hP
        · right; nlinarith
      · right
        have hfull := hch.2 P a hc
        have hge : (P.length : ℝ) ≤ r * tot P := by
          apply tot_ge r P
          intro B hBm
          have := hfull B hBm
          nlinarith
        have hl : (step ch P a).length = P.length + 1 := by
          unfold step; rw [hc, placeAt_eq]; simp
        rw [hl, htot]
        push_cast
        nlinarith

lemma split_sorted (t : ℝ) : ∀ S : List ℝ, S.Pairwise (fun a b => b ≤ a) →
    S = S.filter (fun a => decide (t < a)) ++ S.filter (fun a => !decide (t < a))
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.pairwise_cons] at h
    by_cases hx : t < x
    · have ih := split_sorted t xs h.2
      simp only [List.filter_cons, hx, decide_true, if_true, Bool.not_true]
      simp only [Bool.false_eq_true, if_false, List.cons_append]
      exact congrArg (x :: ·) ih
    · have h1 : xs.filter (fun a => decide (t < a)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have := h.1 y hy
        simp only [decide_eq_true_eq]
        intro hty; exact hx (lt_of_lt_of_le hty this)
      have h2 : xs.filter (fun a => !decide (t < a)) = xs := by
        rw [List.filter_eq_self]
        intro y hy
        have := h.1 y hy
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
        intro hty; exact hx (lt_of_lt_of_le hty this)
      simp only [List.filter_cons, hx, decide_false, Bool.false_eq_true, if_false, Bool.not_false,
        if_true, h1, h2, List.nil_append]

lemma opt_nonempty (L : List ℝ) (hL : IsList L) : {b : ℕ | ∃ f : Fin L.length → Fin b,
    ∀ j : Fin b, ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}.Nonempty := by
  refine ⟨L.length, fun i => i, ?_⟩
  intro j
  have : Finset.univ.filter (fun i : Fin L.length => i = j) = {j} := by
    ext x; simp
  rw [this, Finset.sum_singleton]
  exact (hL _ (List.get_mem L j)).2

lemma sum_le_optBins (L : List ℝ) (hL : IsList L) : L.sum ≤ (optBins L : ℝ) := by
  obtain ⟨f, hf⟩ := Nat.sInf_mem (opt_nonempty L hL)
  have hsum : L.sum = ∑ i : Fin L.length, L.get i := by
    rw [← List.sum_ofFn, List.ofFn_get]
  unfold optBins
  rw [hsum, ← Finset.sum_fiberwise Finset.univ f (fun i => L.get i)]
  calc _ ≤ ∑ _j : Fin (sInf {b : ℕ | ∃ f : Fin L.length → Fin b, ∀ j : Fin b,
        ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i ≤ 1}), (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hf j)
    _ = _ := by simp

lemma optBins_mono (L : List ℝ) (hL : IsList L) (p : ℝ → Bool) :
    optBins (L.filter p) ≤ optBins L := by
  obtain ⟨f, hf⟩ := Nat.sInf_mem (opt_nonempty L hL)
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp (List.filter_sublist (p := p) (l := L))
  unfold optBins
  apply Nat.sInf_le
  refine ⟨fun i => f (e i), fun j => ?_⟩
  calc ∑ i ∈ Finset.univ.filter (fun i => f (e i) = j), (L.filter p).get i
      = ∑ i ∈ (Finset.univ.filter (fun i => f (e i) = j)).map e.toEmbedding, L.get i := by
        rw [Finset.sum_map]; exact Finset.sum_congr rfl (fun i _ => he i)
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i => f i = j), L.get i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          obtain ⟨a, ha, rfl⟩ := hx
          exact ha
        · intro i _ _; exact (hL _ (List.get_mem L i)).1.le
    _ ≤ 1 := hf j

lemma sorted_sortDesc (L : List ℝ) : (sortDesc L).Pairwise (fun a b => b ≤ a) := by
  have := List.pairwise_mergeSort (le := fun a b : ℝ => decide (b ≤ a))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; linarith)
    (fun a b => by simp; exact le_total b a) L
  exact this.imp (fun h => by simpa using h)

lemma main (ch : List (List ℝ) → ℝ → ℕ) (hch : GoodChoice ch)
    (L : List ℝ) (hL : IsList L) (r d : ℝ) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (h : r * (optBins L : ℝ) + d < ((run ch (sortDesc L)).length : ℝ)) :
    r * (optBins (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) + d <
      ((run ch (sortDesc (L.filter (fun a => decide ((r - 1) / r < a))))).length : ℝ) := by
  have hr0 : 0 < r := by linarith
  set t := (r - 1) / r with ht
  set S := sortDesc L with hSdef
  have hperm : S.Perm L := List.mergeSort_perm _ _
  have hS := sorted_sortDesc L
  have hsplit := split_sorted t S hS
  have hsd : sortDesc (L.filter (fun a => decide (t < a))) = S.filter (fun a => decide (t < a)) := by
    apply List.Perm.eq_of_sortedGE
    · exact List.Pairwise.sortedGE ((sorted_sortDesc _).imp (fun h => h))
    · exact List.Pairwise.sortedGE ((hS.filter _).imp (fun h => h))
    · exact (List.mergeSort_perm _ _).trans (hperm.filter _).symm
  have hrun : ∀ M : List ℝ, run ch M = M.foldl (step ch) [] := fun M => rfl
  have hFFD : (run ch S).length = ((S.filter (fun a => !decide (t < a))).foldl (step ch)
      (run ch (S.filter (fun a => decide (t < a))))).length := by
    rw [hrun, hrun]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append]
  have hFFD' : (run ch (sortDesc (L.filter (fun a => decide (t < a))))).length =
      (run ch (S.filter (fun a => decide (t < a)))).length := by
    rw [hsd]
  have htot : tot ((S.filter (fun a => !decide (t < a))).foldl (step ch)
      (run ch (S.filter (fun a => decide (t < a))))) = L.sum := by
    rw [tot_fold ch hch]
    have h0 : tot (run ch (S.filter (fun a => decide (t < a)))) =
        (S.filter (fun a => decide (t < a))).sum := by
      rw [hrun, tot_fold ch hch]
      simp [tot]
    rw [h0, ← List.sum_append, ← hsplit, hperm.sum_eq]
  have hsmall : ∀ a ∈ S.filter (fun a => !decide (t < a)), 0 < a ∧ r * a ≤ r - 1 := by
    intro a ha
    rw [List.mem_filter] at ha
    have hmem : a ∈ L := hperm.mem_iff.mp ha.1
    refine ⟨(hL a hmem).1, ?_⟩
    have hle : a ≤ t := by simpa using ha.2
    rw [ht, le_div_iff₀ hr0] at hle
    linarith
  have hinv := small_phase ch hch r hr0 (run ch (S.filter (fun a => decide (t < a)))).length
    (S.filter (fun a => !decide (t < a))) (run ch (S.filter (fun a => decide (t < a)))) hsmall
    (Or.inl rfl)
  rw [← hFFD, htot] at hinv
  have hopt := sum_le_optBins L hL
  have hmono := optBins_mono L hL (fun a => decide (t < a))
  rcases hinv with h1 | h1
  · rw [hFFD', ← h1]
    have : (optBins (L.filter (fun a => decide (t < a))) : ℝ) ≤ optBins L := by exact_mod_cast hmono
    nlinarith
  · exfalso
    nlinarith

end DSAux_7337ec4c

open DSAux_7337ec4c in
open BinPacking.Decreasing in
theorem solution (L : List ℝ) (hL : IsList L) (r d : ℝ) (hr : 1 ≤ r) (hd : 1 ≤ d) :
    ((FFD L : ℝ) > r * (optBins L : ℝ) + d →
      (FFD (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) >
        r * (optBins (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) + d) ∧
    ((BFD L : ℝ) > r * (optBins L : ℝ) + d →
      (BFD (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) >
        r * (optBins (L.filter (fun a => decide ((r - 1) / r < a))) : ℝ) + d) := by
  exact ⟨fun h => main ffChoice ff_good L hL r d hr hd h,
    fun h => main bfChoice bf_good L hL r d hr hd h⟩
