-- Prove2me | solution 1 for FixedMachinePrec.evaluate_marked_row_order
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:08:38.524799+00:00
-- url     : https://prove2.me/submissions/6f8dfcb1-9e7b-4ccb-b691-5d1e0a0d2590

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_Hierarchy


open FixedMachinePrec


private theorem union_mem {N} (s : List (Finset (Fin N))) (x) : x ∈ unionSlots s ↔ ∃ A ∈ s, x ∈ A := by
  unfold unionSlots; induction s with | nil => simp | cons A s ih => simp [ih]

private theorem slot_time {N} {s : List (Finset (Fin N))} (hd : s.Pairwise Disjoint) {i} (hi : i < s.length) {x} (hx : x ∈ s[i]) : localTime s x = i+1 := by
  unfold localTime
  congr 1
  apply (List.findIdx_eq hi).mpr
  refine ⟨decide_eq_true hx,?_⟩
  intro j hj; simp only [decide_eq_false_iff_not]
  exact fun h => Finset.disjoint_left.mp (List.pairwise_iff_getElem.mp hd j i (hj.trans hi) hi hj) h hx


private theorem full_count {N m} {p : Fin N → Fin N → Prop} {W S} (hs : IsFullSchedule p m W S) : W.card = m*S.length := by
  obtain ⟨hslot,hdis,hu,horder⟩ := hs
  clear horder
  rw [← hu]; clear hu
  induction S with
  | nil => simp
  | cons a s ih =>
    have hd := List.pairwise_cons.mp hdis
    have dj : Disjoint a (s.foldr (· ∪ ·) ∅) := by
      have aux (l : List (Finset (Fin N))) (h : ∀ b ∈ l, Disjoint a b) : Disjoint a (l.foldr (· ∪ ·) ∅) := by
        induction l with
        | nil => simp
        | cons b l ih => simp [h b (by simp),ih (fun c hc => h c (by simp [hc]))]
      exact aux _ hd.1
    simp only [List.foldr_cons,Finset.card_union_of_disjoint dj,List.length_cons,Nat.mul_add,Nat.mul_one]
    rw [(hslot a (by simp)).1,ih (fun b hb => hslot b (by simp [hb])) hd.2,Nat.add_comm]

private theorem enumerate {N} (A : Finset (Fin N)) : ∃ k < 2^N, decodeSet N k = A := by
  induction A using Finset.induction_on with
  | empty => exact ⟨0,by positivity,by simp [decodeSet]⟩
  | insert a A _ ih =>
    obtain ⟨k,hk,rfl⟩ := ih
    refine ⟨2^a.val ||| k,Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by decide) a.isLt) hk,?_⟩
    ext x; simp [decodeSet,Nat.testBit_two_pow,Fin.ext_iff]; tauto

private theorem codes {N} (F : Finset (Finset (Fin N))) (A) : A ∈ listByCode F ↔ A ∈ F := by
  simp only [listByCode,List.mem_filterMap,List.mem_range]
  constructor
  · rintro ⟨k,hk,e⟩; split at e <;> simp_all
  · intro h; obtain ⟨k,hk,he⟩ := enumerate A; exact ⟨k,hk,by simp [he,h]⟩

private theorem rows_mem {N} (F : Finset (Finset (Fin N))) (A) : A ∈ listByCardCode F ↔ A ∈ F := by
  simp only [listByCardCode,List.mem_flatMap,List.mem_range,List.mem_filter,codes,decide_eq_true_eq]
  constructor
  · rintro ⟨_,_,h,_⟩;exact h
  · intro h; exact ⟨A.card,Nat.lt_succ_of_le (by simpa using A.card_le_univ),h,rfl⟩

private theorem rows_sorted {N} (F : Finset (Finset (Fin N))) :
    (listByCardCode F).Pairwise (fun A B => A.card ≤ B.card) := by
  unfold listByCardCode; apply List.pairwise_flatMap.mpr; constructor
  · intro k _; apply List.pairwise_iff_getElem.mpr; intro i j hi hj hij
    have h1 := (List.mem_filter.mp (List.getElem_mem hi)).2
    have h2 := (List.mem_filter.mp (List.getElem_mem hj)).2
    simp_all
  · apply List.pairwise_le_range.imp
    intro i j h A hA B hB; simp_all

private theorem gap_endpoint (marks : List ℕ) (hne : marks ≠ []) (endpt a b : ℕ)
    (h : (a,b) ∈ (0 :: (marks ++ [endpt])).zip (marks ++ [endpt])) : a ∈ marks ∨ b ∈ marks := by
  have aux (l : List ℕ) (u) (h : (a,b) ∈ (u::(l++[endpt])).zip (l++[endpt])) : a=u ∨ a∈l := by
    induction l generalizing u with
    | nil => simp_all
    | cons v l ih =>
      simp only [List.cons_append,List.zip_cons_cons,List.mem_cons,Prod.mk.injEq] at h
      rcases h with ⟨rfl,_⟩ | ht
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr (ih v ht))
  cases marks with
  | nil => contradiction
  | cons v l =>
    simp only [List.cons_append,List.zip_cons_cons,List.mem_cons,Prod.mk.injEq] at h
    rcases h with ⟨_,rfl⟩|h
    · exact Or.inr (by simp)
    · exact Or.inl (List.mem_cons.mpr (aux l v h))

private theorem gap_smaller {N m} {p : Fin N → Fin N → Prop} {W S} (hs : IsFullSchedule p m W S) (hm : 1 ≤ m)
    {marks : List ℕ} (hk : marks ≠ []) (hr : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length) (A) (hA : A ∈ gaps S marks) : A.card < W.card := by
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp hA
  obtain ⟨t,ht,he⟩ : ∃ t ∈ marks, t=a ∨ t=b := by
    rcases gap_endpoint marks hk (S.length+1) a b hab with h|h
    · exact ⟨a,h,Or.inl rfl⟩
    · exact ⟨b,h,Or.inr rfl⟩
  have hr' := hr t ht
  have idx : t-1 < S.length := by omega
  have lg := (hs.1 _ (List.getElem_mem idx)).1
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0 < S[t-1].card by omega)
  have mem (x i) (hi : i < S.length) (hx : x ∈ S.getD i ∅) : x ∈ W := hs.2.2.1 ▸ (union_mem _ _).mpr ⟨_,List.getElem_mem hi,by simpa [List.getD_eq_getElem?_getD,hi] using hx⟩
  apply Finset.card_lt_card; apply (Finset.ssubset_iff_of_subset ?_).mpr
  · refine ⟨z,mem z _ idx (by simpa [List.getD_eq_getElem?_getD,idx] using hz),?_⟩
    intro hg
    obtain ⟨i,hi,hzi⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨hi,lo,up⟩ := Finset.mem_filter.mp hi
    have hi' := Finset.mem_range.mp hi
    have ht1 := slot_time hs.2.1 idx hz
    have ht2 := slot_time hs.2.1 hi' (x := z) (by simpa [List.getD_eq_getElem?_getD,hi'] using hzi)
    omega
  · intro x hx; obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact mem _ _ (Finset.mem_range.mp (Finset.mem_filter.mp hi).1) hx

private def step {N} (p : Fin N → Fin N → Prop) [DecidableRel p] (m : ℕ) (F C : Finset (Finset (Fin N))) (tab : Table N) (W) :=
  if W = ∅ ∨ ¬ m ∣ W.card then tab else processParent p m F C tab W

private theorem step_other {N} (p : Fin N → Fin N → Prop) [DecidableRel p] (m F C) (tab : Table N) (A W) (h : A ≠ W) : step p m F C tab W A = tab A := by
  unfold step; split
  · rfl
  · unfold processParent; dsimp only; generalize List.find? _ _ = o; cases o <;> simp [Function.update_of_ne h]

private theorem unchanged {N} (p : Fin N → Fin N → Prop) [DecidableRel p] (m F C) (l : List (Finset (Fin N))) (tab : Table N) (A) (h : A ∉ l) : l.foldl (step p m F C) tab A = tab A := by
  induction l generalizing tab with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons,ih _ (by simp_all),step_other _ _ _ _ _ _ _ (by simp_all)]

private theorem persistent {N} (p : Fin N → Fin N → Prop) [DecidableRel p] (m F C) (l : List (Finset (Fin N))) (tab : Table N) (A) (h : (tab A).isSome = true) : ((l.foldl (step p m F C) tab) A).isSome = true := by
  induction l generalizing tab with
  | nil => exact h
  | cons a l ih =>
    apply ih; unfold step; split
    · exact h
    · by_cases eq : A=a
      · subst a; unfold processParent; dsimp only; generalize List.find? _ _ = o; cases o <;> simp [h]
      · unfold processParent; dsimp only; generalize List.find? _ _ = o; cases o <;> simp [Function.update_of_ne eq,h]

theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (hp : IsStrictOrder' prec) (F C : Finset (Finset (Fin N))) (h0 : ∅ ∈ F)
    (W : Finset (Fin N)) (hw : W ∈ F) (hne : W.Nonempty) (S : List (Finset (Fin N)))
    (hs : IsFullSchedule prec m W S) (marks : List ℕ) (hk : marks ≠ [])
    (hi : marks.Pairwise (· < ·)) (hr : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length)
    (hc : ∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X)
(hg : ∀ A ∈ gaps S marks, (evaluateFamily prec m F C A).isSome = true)
    (hstep : ∀ tab : Table N, (∀ A ∈ gaps S marks, (lookup F tab A).isSome = true) →
      (processParent prec m F C tab W W).isSome = true) : (evaluateFamily prec m F C W).isSome = true := by
  let init : Table N := fun X => if X = ∅ ∧ (∅ : Finset (Fin N)) ∈ F then some [] else none
  let f := step prec m F C
  have ev : evaluateFamily prec m F C = (listByCardCode F).foldl f init := rfl
  obtain ⟨left,right,eq⟩ := List.append_of_mem ((rows_mem F W).mpr hw)
  have after := (List.pairwise_cons.mp (List.pairwise_append.mp (eq ▸ rows_sorted F)).2.1).1
  let tab := left.foldl f init
  have got (A) (ha : A ∈ gaps S marks) : (lookup F tab A).isSome = true := by
    have lt := gap_smaller hs hm hk hr A ha
    have memF : A ∈ F := by
      by_contra hn
      have absent : A ∉ listByCardCode F := fun h => hn ((rows_mem F A).mp h)
      have h := hg A ha; rw [ev,unchanged] at h
      · simp [init] at h; grind
      · exact absent
    have h := hg A ha
    rw [ev,eq,List.foldl_append] at h
    have hn : A ∉ W::right := by intro hx; rcases List.mem_cons.mp hx with e|h; subst A;omega;have := after A h;omega
    rw [unchanged _ _ _ _ _ _ _ hn] at h
    simpa [lookup,memF,tab] using h
  have div : m ∣ W.card := ⟨S.length,full_count hs⟩
  rw [ev,eq,List.foldl_append,List.foldl_cons]
  apply persistent
  simpa [f,step,hne.ne_empty,div] using hstep tab got
