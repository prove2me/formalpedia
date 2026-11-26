-- Prove2me | solution 1 for FixedMachinePrec.bucket_pass_closed
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:42:43.087609+00:00
-- url     : https://prove2.me/submissions/5033b8ca-81f3-4a2b-b563-7769a8db301d

import Definitions.Def_FixedMachinePrec_EvaluateFamily

open FixedMachinePrec

private abbrev PassState := (ℕ → Bool) × (ℕ → PredField)
private def relax (e : ℕ → ℕ → Bool) (i : ℕ) (v : PassState) (j : ℕ) : PassState :=
  if !v.1 j && e i j then (Function.update v.1 j true,Function.update v.2 j (.pred i)) else v
private def visit (s : ℕ) (e : ℕ → ℕ → Bool) (v : PassState) (i : ℕ) :=
  if v.1 i then (List.range s).foldl (relax e i) v else v

private theorem relax_spec (e) (i j : ℕ) (l : List ℕ) (v : PassState) :
    (l.foldl (relax e i) v).1 j = true ↔ v.1 j = true ∨ j ∈ l ∧ e i j = true := by
  induction l generalizing v with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons,ih,List.mem_cons]
    by_cases h : j = a
    · subst a; unfold relax; split <;> simp_all <;> grind
    · unfold relax; split <;> simp_all [Function.update_of_ne h] <;> grind

private theorem visit_spec (s e v i j) :
    (visit s e v i).1 j = true ↔ v.1 j = true ∨ v.1 i = true ∧ j < s ∧ e i j = true := by
  unfold visit; split <;> simp_all [relax_spec]

private theorem keeps_mark (s e) (xs : List ℕ) (v : PassState) (i) (h : v.1 i = true) :
    (xs.foldl (visit s e) v).1 i = true := by
  induction xs generalizing v with
  | nil => exact h
  | cons a xs ih => exact ih _ ((visit_spec ..).mpr (Or.inl h))

private theorem no_incoming (s e) (xs : List ℕ) (v : PassState) (i) (h : ∀ x ∈ xs, e x i ≠ true) :
    (xs.foldl (visit s e) v).1 i = true → v.1 i = true := by
  induction xs generalizing v with
  | nil => exact id
  | cons a xs ih =>
    intro hit
    have hstep := ih (visit s e v a) (fun x hx => h x (by simp [hx])) hit
    rcases (visit_spec ..).mp hstep with old | ⟨_,_,ha⟩
    · exact old
    · exact False.elim (h a (by simp) ha)

private theorem forward_closed (s : ℕ) (e : ℕ → ℕ → Bool) (w : ℕ → ℕ) (order : List ℕ) (v : PassState)
    (hs : order.Pairwise (fun i j => w i ≤ w j))
    (hedge : ∀ i j, e i j = true → i ∈ order ∧ j < s ∧ w i < w j) (i j)
    (hi : (order.foldl (visit s e) v).1 i = true) (he : e i j = true) :
    (order.foldl (visit s e) v).1 j = true := by
  obtain ⟨hin,hj,hlt⟩ := hedge i j he
  obtain ⟨before,after,rfl⟩ := List.append_of_mem hin
  have sorted := (List.pairwise_cons.mp (List.pairwise_append.mp hs).2.1).1
  simp only [List.foldl_append,List.foldl_cons] at hi ⊢
  have atVisit := no_incoming s e after _ i (fun x hx hxi => (hedge x i hxi).2.2.not_ge (sorted x hx)) hi
  have marked : (before.foldl (visit s e) v).1 i = true := by
    rcases (visit_spec ..).mp atVisit with h | ⟨h,_,_⟩ <;> exact h
  exact keeps_mark _ _ _ _ _ ((visit_spec ..).mpr (Or.inr ⟨marked,hj,he⟩))

private theorem prefix_grows {N m : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (C : Finset (Finset (Fin N))) (W : Finset (Fin N)) (hm : 1 ≤ m) (a) (ha : a ∈ buildStates prec m C W) :
    a.L ⊂ a.L ∪ a.Z := by
  unfold buildStates at ha
  obtain ⟨cut,_,h⟩ := List.mem_flatMap.mp ha
  dsimp only at h
  split at h
  · obtain ⟨Z,hZ,he⟩ := List.mem_filterMap.mp h
    obtain ⟨hset,hsub⟩ := List.mem_filter.mp hZ
    simp only [decide_eq_true_eq] at hsub
    unfold mSubsetsLex at hset
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hset
    obtain ⟨_,hlen⟩ := List.mem_sublistsLen.mp (List.mem_mergeSort.mp hl)
    have hn : l ≠ [] := by rintro rfl; simp only [List.length_nil] at hlen; omega
    obtain ⟨z,hz⟩ := List.exists_mem_of_ne_nil l hn
    split at he
    · cases he
      apply (Finset.ssubset_iff_of_subset Finset.subset_union_left).mpr
      exact ⟨z,Finset.mem_union_right _ (List.mem_toFinset.mpr hz),(Finset.mem_sdiff.mp (hsub (List.mem_toFinset.mpr hz))).2⟩
    · contradiction
  · contradiction

private def bucket {N : ℕ} (st : List (StateRec N)) (c : ℕ) :=
  (List.range st.length).filter fun i => match st[i]? with | some a => decide (a.L.card = c) | none => false
private def weight {N : ℕ} (st : List (StateRec N)) (i : ℕ) := (st[i]?.map fun a => a.L.card).getD 0
private theorem bucket_weight {N : ℕ} (st : List (StateRec N)) (c i) (h : i ∈ bucket st c) : weight st i = c := by
  obtain ⟨_,hc⟩ := List.mem_filter.mp h
  unfold weight
  split at hc <;> simp_all

private theorem bucket_order {N : ℕ} (st : List (StateRec N)) :
    ((List.range (N+1)).flatMap (bucket st)).Pairwise (fun i j => weight st i ≤ weight st j) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro c _
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj _
    rw [bucket_weight st c _ (List.getElem_mem hi),bucket_weight st c _ (List.getElem_mem hj)]
  · apply List.pairwise_le_range.imp
    intro c d h i hi j hj
    simpa only [bucket_weight st c i hi,bucket_weight st d j hj] using h

theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (C : Finset (Finset (Fin N))) (W : Finset (Fin N)) (lk : Finset (Fin N) → Bool) : let st := buildStates prec m C W; let marked := (reachPass st lk).1; (∀ i a, st[i]? = some a → lk a.L = true → marked i = true) ∧ (∀ i j, marked i = true → edge st lk i j = true → marked j = true) := by
  let st := buildStates prec m C W
  let order := (List.range (N+1)).flatMap (bucket st)
  let start : ℕ → Bool := fun i => match st[i]? with | some a => lk a.L | none => false
  let v : PassState := (start,fun i => if start i then .start else .unreached)
  change (∀ i a, st[i]? = some a → lk a.L = true → (order.foldl (visit st.length (edge st lk)) v).1 i = true) ∧ _
  constructor
  · intro i a hi hl; apply keeps_mark; simp [v,start,hi,hl]
  · apply forward_closed st.length (edge st lk) (weight st) order v (bucket_order st)
    intro i j he
    unfold edge at he
    split at he
    · rename_i a b ha hb
      have ii : i < st.length := by by_contra! h; simp [List.getElem?_eq_none h] at ha
      have jj : j < st.length := by by_contra! h; simp [List.getElem?_eq_none h] at hb
      have hsub := of_decide_eq_true (Bool.and_eq_true_iff.mp he).1
      have grow := prefix_grows prec C W hm a (List.mem_of_getElem? ha)
      refine ⟨List.mem_flatMap.mpr ⟨a.L.card,List.mem_range.mpr (Nat.lt_succ_of_le (by simpa using a.L.card_le_univ)),?_⟩,jj,?_⟩
      · exact List.mem_filter.mpr ⟨List.mem_range.mpr ii,by simp [ha]⟩
      · simpa [weight,ha,hb] using (Finset.card_lt_card grow).trans_le (Finset.card_le_card hsub)
    · contradiction
