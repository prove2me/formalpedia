-- Prove2me | solution 1 for FixedMachinePrec.pass_trace_certificate
-- status  : ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T12:41:04.753237+00:00
-- url     : https://prove2.me/submissions/e830e3b2-37ce-4b29-b2e6-16fbb6781692

import Definitions.Def_FixedMachinePrec_EvaluateFamily

open FixedMachinePrec

private abbrev PassState := (ℕ → Bool) × (ℕ → PredField)
private def marks (s : ℕ) (r : ℕ → Bool) := (Finset.range s).filter (fun i => r i = true)
private def Ranked (s : ℕ) (initial : ℕ → Prop) (E : ℕ → ℕ → Prop) (rp : PassState) :=
  ∃ d : ℕ → ℕ, ∀ i, rp.1 i = true → i < s ∧ d i < (marks s rp.1).card ∧
    ((rp.2 i = .start ∧ initial i) ∨ ∃ a, rp.2 i = .pred a ∧ rp.1 a = true ∧ d a < d i ∧ E a i)

private theorem extend_rank {s init E rp} (ok : Ranked s init E rp) {a b : ℕ}
    (ha : rp.1 a = true) (hb : rp.1 b = false) (hs : b < s) (he : E a b) :
    Ranked s init E (Function.update rp.1 b true, Function.update rp.2 b (.pred a)) := by
  obtain ⟨d, hd⟩ := ok
  let D := (marks s rp.1).card
  let r' := Function.update rp.1 b true
  have holds (x) (hx : rp.1 x = true) : x ≠ b := fun e => by subst x; simp_all
  have keep (x) (hx : rp.1 x = true) : r' x = true := by simp [r',Function.update_of_ne (holds x hx),hx]
  have more : D < (marks s r').card := by
    apply Finset.card_lt_card
    apply (Finset.ssubset_iff_of_subset ?_).mpr
    · exact ⟨b,by simp [marks,r',hs],by simp [marks,hb]⟩
    · intro x hx
      simp only [marks,Finset.mem_filter,Finset.mem_range] at hx ⊢
      exact ⟨hx.1,keep x hx.2⟩
  refine ⟨Function.update d b D,?_⟩
  intro x hx
  by_cases eq : x = b
  · subst x
    refine ⟨hs,by simpa using more,Or.inr ⟨a,by simp,keep a ha,?_,he⟩⟩
    simpa [Function.update_of_ne (holds a ha)] using (hd a ha).2.1
  · have old : rp.1 x = true := by simpa [Function.update_of_ne eq] using hx
    obtain ⟨hlt,hdepth,hpred⟩ := hd x old
    refine ⟨hlt,by simpa [Function.update_of_ne eq] using hdepth.trans more,?_⟩
    simp only [Function.update_of_ne eq]
    rcases hpred with start | ⟨i,hi,hr,hlt',he'⟩
    · exact Or.inl start
    · exact Or.inr ⟨i,hi,keep i hr,by simpa [Function.update_of_ne (holds i hr)] using hlt',he'⟩

private theorem fold_keeps {α β : Type*} (P : β → Prop) (f : β → α → β) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b, P b → P (f b x)) (b : β) (hb : P b) : P (xs.foldl f b) := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih => exact ih (fun x hx => h x (by simp [hx])) _ (h a (by simp) b hb)

private theorem pass_ranked {N} (st : List (StateRec N)) (lk : Finset (Fin N) → Bool) :
    Ranked st.length (fun i => ∃ a, st[i]? = some a ∧ lk a.L = true)
      (fun i j => edge st lk i j = true) (reachPass st lk) := by
  let Ok := Ranked st.length (fun i => ∃ a, st[i]? = some a ∧ lk a.L = true) (fun i j => edge st lk i j = true)
  change Ok _
  unfold reachPass
  apply fold_keeps Ok
  · intro a _ rp ok
    split
    · rename_i ha
      refine (fold_keeps (fun v : PassState => Ok v ∧ v.1 a = true) _ _ ?_ rp ⟨ok,ha⟩).1
      · intro b hb v hv
        split
        · rename_i hstep
          obtain ⟨hu,he⟩ := Bool.and_eq_true_iff.mp hstep
          have hu' : v.1 b = false := by simpa using hu
          have hn : a ≠ b := by intro e; subst b; simp_all
          exact ⟨extend_rank hv.1 hv.2 hu' (List.mem_range.mp hb) he, by simpa [Function.update_of_ne hn] using hv.2⟩
        · exact hv
    · exact ok
  · refine ⟨fun _ => 0,?_⟩
    intro i hi
    dsimp only at hi ⊢
    have initial : ∃ a, st[i]? = some a ∧ lk a.L = true := by
      split at hi
      · exact ⟨_,by assumption,hi⟩
      · contradiction
    obtain ⟨a,he,hL⟩ := initial
    have hlt : i < st.length := by by_contra! hn; simp [List.getElem?_eq_none hn] at he
    refine ⟨hlt,Finset.card_pos.mpr ⟨i,?_⟩,Or.inl ⟨?_,a,he,hL⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,hi⟩
    · simp only [hi,if_true]

private theorem trace_of_rank {s init E rp} (ok : Ranked s init E rp) (j : ℕ) (hj : rp.1 j = true) :
    let path := tracePath rp.2 s j
    ∃ i rest, path = i :: rest ∧ init i ∧ rp.2 i = .start ∧ path.getLast? = some j ∧ path.IsChain E := by
  obtain ⟨d,hd⟩ := ok
  have aux (fuel j : ℕ) (hj : rp.1 j = true) (h : d j < fuel) :
      let path := tracePath rp.2 fuel j
      ∃ i rest, path = i :: rest ∧ init i ∧ rp.2 i = .start ∧ path.getLast? = some j ∧ path.IsChain E := by
    induction fuel generalizing j with
    | zero => omega
    | succ fuel ih =>
      rcases (hd j hj).2.2 with ⟨hs,hi⟩ | ⟨a,hp,ha,hlt,he⟩
      · exact ⟨j,[],by simp [tracePath,hs],hi,hs,by simp [tracePath,hs],by simp [tracePath,hs]⟩
      · obtain ⟨i,rest,hpath,hi,hs,hl,hc⟩ := ih a ha (by omega)
        simp only [tracePath,hp]
        refine ⟨i,rest ++ [j],by simp [hpath],hi,hs,by simp, hc.append (by simp) ?_⟩
        simpa [hl] using he
  have hc : (marks s rp.1).card ≤ s := by simpa [marks] using Finset.card_le_card (Finset.filter_subset (fun i => rp.1 i = true) (Finset.range s))
  exact aux s j hj ((hd j hj).2.1.trans_le hc)

theorem solution {N : ℕ} (st : List (StateRec N)) (lk : Finset (Fin N) → Bool) (j : ℕ) (_hj : j < st.length) (hm : (reachPass st lk).1 j = true) : let p := (reachPass st lk).2; let path := tracePath p st.length j; ∃ i rest, path = i :: rest ∧ (∃ a, st[i]? = some a ∧ lk a.L = true) ∧ p i = .start ∧ path.getLast? = some j ∧ path.IsChain (fun x y => edge st lk x y = true) := by
  exact trace_of_rank (pass_ranked st lk) j hm
