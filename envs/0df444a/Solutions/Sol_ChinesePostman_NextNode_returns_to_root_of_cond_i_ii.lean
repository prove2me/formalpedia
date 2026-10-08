-- Prove2me | solution 1 for ChinesePostman.NextNode.returns_to_root_of_cond_i_ii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T07:47:49.568956+00:00
-- url     : https://prove2.me/submissions/2f25ec36-2190-4491-ae4f-140b7c3bec3a

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting



namespace ChinesePostman.NextNode

def prs {V : Type} (ns : List V) : List (V × V) := ns.zip ns.tail

lemma prs_cons_cons {V : Type} (a b : V) (l : List V) : prs (a :: b :: l) = (a, b) :: prs (b :: l) := by
  simp [prs]

lemma prs_single {V : Type} (a : V) : prs [a] = [] := by simp [prs]

lemma followAux_spec {V : Type} [DecidableEq V] (L : V → List V) (fuel : ℕ) :
    ∀ (u : V) (t : V → ℕ),
    (followAux L fuel u t).1 ≠ [] ∧ (followAux L fuel u t).1.head? = some u ∧
    (∀ a, (followAux L fuel u t).2 a = t a + ((followAux L fuel u t).1.dropLast).count a) ∧
    (∀ a b, (unused L t a).count b =
      (unused L (followAux L fuel u t).2 a).count b + ((prs (followAux L fuel u t).1).count (a, b))) ∧
    (∀ a, (unused L t a).reverse = (((prs (followAux L fuel u t).1).filter (fun p => p.1 = a)).map Prod.snd) ++
      (unused L (followAux L fuel u t).2 a).reverse) := by
  induction fuel with
  | zero =>
    intro u t
    simp [followAux, prs_single]
  | succ fuel ih =>
    intro u t
    unfold followAux
    cases hn : nextState L u t with
    | none => simp [prs_single]
    | some pr =>
      obtain ⟨v, t'⟩ := pr
      simp only
      unfold nextState at hn
      split_ifs at hn with hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨hv, ht'⟩ := hn
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih v t'
      set p := followAux L fuel v t' with hp
      obtain ⟨rest, hrest⟩ : ∃ rest, p.1 = v :: rest := by
        cases hh : p.1 with
        | nil => exact absurd hh h1
        | cons x r => rw [hh] at h2; simp at h2; exact ⟨r, by rw [h2]⟩
      have hdl : (u :: p.1).dropLast = u :: p.1.dropLast := List.dropLast_cons_of_ne_nil h1
      have hpr : prs (u :: p.1) = (u, v) :: prs p.1 := by rw [hrest, prs_cons_cons]
      refine ⟨by simp, by simp, ?_, ?_, ?_⟩
      · intro a
        rw [h3 a, ← ht', hdl]
        by_cases hau : a = u
        · subst hau
          simp [Function.update, List.count_cons]
          omega
        · simp [Function.update, hau, List.count_cons, Ne.symm hau]
      · intro a b
        have := h4 a b
        rw [hpr]
        by_cases hau : a = u
        · subst hau
          have hun : unused L t a = unused L t' a ++ [v] := by
            have hi : (L a).length - (t a + 1) < (L a).length := by omega
            have hv' : (L a)[(L a).length - (t a + 1)]'hi = v := by
              rw [← hv]; congr 1; omega
            simp only [unused, ← ht', Function.update_self]
            have : (L a).length - t a = ((L a).length - (t a + 1)) + 1 := by omega
            rw [this, List.take_succ, List.getElem?_eq_getElem hi, hv']
            rfl
          rw [hun, List.count_append, this]
          simp [List.count_cons, List.count_singleton]
          omega
        · have hun : unused L t a = unused L t' a := by
            simp [unused, ← ht', Function.update, hau]
          rw [hun, this]
          simp [List.count_cons, hau]
          intro h; exact absurd h.symm hau
      · intro a
        have := h5 a
        by_cases hau : a = u
        · subst hau
          have hun : unused L t a = unused L t' a ++ [v] := by
            have hi : (L a).length - (t a + 1) < (L a).length := by omega
            have hv' : (L a)[(L a).length - (t a + 1)]'hi = v := by
              rw [← hv]; congr 1; omega
            simp only [unused, ← ht', Function.update_self]
            have : (L a).length - t a = ((L a).length - (t a + 1)) + 1 := by omega
            rw [this, List.take_succ, List.getElem?_eq_getElem hi, hv']
            rfl
          rw [hun, hpr, List.reverse_append, this]
          simp
        · have hun : unused L t a = unused L t' a := by
            simp [unused, ← ht', Function.update, hau]
          rw [hun, hpr, this]
          simp [List.filter_cons, hau, Ne.symm hau]

lemma followAux_bound {V : Type} [DecidableEq V] (L : V → List V) (fuel : ℕ) :
    ∀ (u : V) (t : V → ℕ), (∀ a, t a ≤ (L a).length) → ∀ a, (followAux L fuel u t).2 a ≤ (L a).length := by
  induction fuel with
  | zero => intro u t ht a; simpa [followAux] using ht a
  | succ fuel ih =>
    intro u t ht a
    unfold followAux
    cases hn : nextState L u t with
    | none => simpa using ht a
    | some pr =>
      obtain ⟨v, t'⟩ := pr
      simp only
      unfold nextState at hn
      split_ifs at hn with hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨hv, ht'⟩ := hn
      apply ih v t' _ a
      intro c
      rw [← ht']
      by_cases hc : c = u
      · subst hc; simp; omega
      · simp [Function.update, hc, ht c]

lemma followAux_end {V : Type} [Fintype V] [DecidableEq V] (L : V → List V) (fuel : ℕ) :
    ∀ (u : V) (t : V → ℕ), ∑ a, ((L a).length - t a) ≤ fuel →
      ∀ w, (followAux L fuel u t).1.getLast? = some w → (L w).length ≤ (followAux L fuel u t).2 w := by
  induction fuel with
  | zero =>
    intro u t hs w hw
    have h0 : ∀ a ∈ Finset.univ, (L a).length - t a = 0 := by
      apply (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hs))
    simp only [followAux, List.getLast?_singleton, Option.some.injEq] at hw
    rw [← hw]
    simp only [followAux]
    have := h0 u (Finset.mem_univ _)
    omega
  | succ fuel ih =>
    intro u t hs w hw
    unfold followAux at hw ⊢
    cases hn : nextState L u t with
    | none =>
      rw [hn] at hw
      simp only [List.getLast?_singleton, Option.some.injEq] at hw
      subst hw
      unfold nextState at hn
      simp only [dite_eq_right_iff, reduceCtorEq, imp_false, not_lt] at hn
      simpa using hn
    | some pr =>
      obtain ⟨v, t'⟩ := pr
      rw [hn] at hw
      simp only at hw ⊢
      unfold nextState at hn
      split_ifs at hn with hlt
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨hv, ht'⟩ := hn
      obtain ⟨h1, _, _, _, _⟩ := followAux_spec L fuel v t'
      have hw' : (followAux L fuel v t').1.getLast? = some w := by
        obtain ⟨x, rest, hrest⟩ : ∃ x l, (followAux L fuel v t').1 = x :: l := by
          cases hh : (followAux L fuel v t').1 with
          | nil => exact absurd hh h1
          | cons x r => exact ⟨x, r, rfl⟩
        rw [hrest] at hw ⊢
        simpa [List.getLast?_cons_cons] using hw
      refine ih v t' ?_ w hw'
      rw [← ht']
      have e1 := Finset.add_sum_erase Finset.univ (fun a => (L a).length - t a) (Finset.mem_univ u)
      have e2 := Finset.add_sum_erase Finset.univ (fun a => (L a).length - Function.update t u (t u + 1) a) (Finset.mem_univ u)
      have e3 : ∑ a ∈ Finset.univ.erase u, ((L a).length - Function.update t u (t u + 1) a) =
          ∑ a ∈ Finset.univ.erase u, ((L a).length - t a) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp [Function.update, Finset.ne_of_mem_erase ha]
      simp only [Function.update_self] at e2
      omega

lemma walk_ends {V E : Type} (G : Graph V E) (ns : List V) (es : List E) (h : IsWalk G ns es) :
    es.map G.ends = (prs ns).map (fun p => s(p.1, p.2)) := by
  obtain ⟨hlen, hw⟩ := h
  apply List.ext_getElem
  · simp [prs, hlen]
  · intro i h1 h2
    have hi : i < es.length := by simpa using h1
    simp only [List.getElem_map, prs, List.getElem_zip, List.getElem_tail]
    exact hw i hi

lemma euler_counts {V E : Type} [Fintype E] [DecidableEq E] (G : Graph V E) (ns : List V) (es : List E)
    (h : IsEulerTour G ns es) :
    (∀ p ∈ prs ns, p.1 ≠ p.2) ∧
    (∀ (P : Sym2 V → Prop) [DecidablePred P],
      (Finset.univ.filter (fun e => P (G.ends e))).card = (prs ns).countP (fun p => decide (P s(p.1, p.2)))) := by
  obtain ⟨hT, hc⟩ := h
  have hE := walk_ends G ns es hT.1
  have hnd : es.Nodup := List.nodup_iff_count_le_one.2 (fun e => (hc e).le)
  have hmem : ∀ e, e ∈ es := fun e => List.count_pos_iff.1 (by rw [hc e]; exact Nat.one_pos)
  constructor
  · intro p hp
    have : s(p.1, p.2) ∈ es.map G.ends := by
      rw [hE]; exact List.mem_map_of_mem hp
    obtain ⟨e, _, he⟩ := List.mem_map.1 this
    have := G.loopless e
    rw [he] at this
    intro hh
    exact this (by simp [hh])
  · intro P _
    have h1 : (Finset.univ.filter (fun e => P (G.ends e))).card = (es.filter (fun e => decide (P (G.ends e)))).length := by
      have : (es.filter (fun e => decide (P (G.ends e)))).toFinset = Finset.univ.filter (fun e => P (G.ends e)) := by
        ext e; simp [hmem e]
      rw [← this, List.toFinset_card_of_nodup (hnd.filter _)]
    rw [h1, ← List.countP_eq_length_filter]
    have := congrArg (List.countP (fun s => decide (P s))) hE
    rw [List.countP_map, List.countP_map] at this
    exact this

lemma countP_fst {V : Type} [DecidableEq V] (ns : List V) (n : V) :
    (prs ns).countP (fun p => decide (p.1 = n)) = ns.dropLast.count n := by
  induction ns with
  | nil => simp [prs]
  | cons a l ih =>
    cases l with
    | nil => simp [prs_single]
    | cons b l =>
      rw [prs_cons_cons, List.countP_cons, ih]
      have : (a :: b :: l).dropLast = a :: (b :: l).dropLast := rfl
      rw [this]
      by_cases h : a = n <;> simp [List.count_cons, h]

lemma countP_snd {V : Type} [DecidableEq V] (ns : List V) (n : V) :
    (prs ns).countP (fun p => decide (p.2 = n)) = ns.tail.count n := by
  induction ns with
  | nil => simp [prs]
  | cons a l ih =>
    cases l with
    | nil => simp [prs_single]
    | cons b l =>
      rw [prs_cons_cons, List.countP_cons, ih]
      have : (a :: b :: l).tail = b :: l := rfl
      rw [this]
      by_cases h : b = n <;> simp [List.count_cons, h]

lemma count_tail_eq_dropLast {V : Type} [DecidableEq V] (ns : List V) (hne : ns ≠ [])
    (hcl : ns.head? = ns.getLast?) (n : V) : ns.tail.count n = ns.dropLast.count n := by
  obtain ⟨x, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have h1 : (x :: rest).count n = (x :: rest).dropLast.count n + (if (x :: rest).getLast hne = n then 1 else 0) := by
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.count_append]
    by_cases h : (x :: rest).getLast hne = n <;> simp [List.count_cons, h]
  have h2 : (x :: rest).count n = rest.count n + (if x = n then 1 else 0) := by
    by_cases h : x = n <;> simp [List.count_cons, h]
  have h3 : (x :: rest).getLast hne = x := by
    rw [List.getLast?_eq_getLast_of_ne_nil hne] at hcl
    simpa using hcl.symm
  simp only [List.tail_cons]
  rw [h3] at h1
  omega

lemma countP_split {V : Type} [DecidableEq V] (l : List (V × V)) (hl : ∀ p ∈ l, p.1 ≠ p.2) (n : V) :
    l.countP (fun p => decide (n ∈ s(p.1, p.2))) =
      l.countP (fun p => decide (p.1 = n)) + l.countP (fun p => decide (p.2 = n)) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have hp := hl p (List.mem_cons_self)
    rw [List.countP_cons, List.countP_cons, List.countP_cons, this]
    by_cases h1 : p.1 = n
    · have : p.2 ≠ n := fun h => hp (h1.trans h.symm)
      simp [h1, this, Sym2.mem_iff]
      omega
    · by_cases h2 : p.2 = n
      · simp [h1, h2, Sym2.mem_iff]
        omega
      · simp [h1, h2, Sym2.mem_iff, Ne.symm h1, Ne.symm h2]

lemma countP_edge {V : Type} [DecidableEq V] (l : List (V × V)) (hl : ∀ p ∈ l, p.1 ≠ p.2) (n m : V)
    (hnm : n ≠ m) :
    l.countP (fun p => decide (s(p.1, p.2) = s(n, m))) = l.count (n, m) + l.count (m, n) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    rw [List.countP_cons, List.count_cons, List.count_cons, this]
    obtain ⟨a, b⟩ := p
    have key : (s(a, b) = s(n, m)) ↔ ((a, b) = (n, m) ∨ (a, b) = (m, n)) := by
      simp [Sym2.eq_iff]
    by_cases h1 : (a, b) = (n, m)
    · have h2 : (a, b) ≠ (m, n) := by
        intro h; apply hnm; rw [Prod.mk.injEq] at h1 h; exact h1.1.symm.trans h.1
      simp [key, h1, h2, hnm, hnm.symm]
      omega
    · by_cases h2 : (a, b) = (m, n)
      · simp [key, h1, h2, hnm, hnm.symm]
        omega
      · simp [key, h1, h2]

lemma follow_facts {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : Graph V E) (r : V) (L : V → List V) (h : DescribesEulerTour G r L) :
    (follow L r).1 ≠ [] ∧
    (∀ a, ((follow L r).1.dropLast).count a = (L a).length) ∧
    (∀ a b, (L a).count b = ((prs (follow L r).1).count (a, b))) := by
  obtain ⟨hall, es, htour⟩ := h
  obtain ⟨h1, h2, h3, h4, -⟩ := followAux_spec L (totalEntries L) r (fun _ => 0)
  refine ⟨h1, ?_, ?_⟩
  · intro a
    have := h3 a
    have h5 := hall a
    unfold follow at h5 ⊢
    omega
  · intro a b
    have := h4 a b
    have h5 := hall a
    unfold follow at h5 ⊢
    simp only [unused, h5, Nat.sub_self, List.take_zero, List.count_nil, Nat.sub_zero, List.take_length] at this
    omega

theorem cond_i_ii_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (r : V) (L : V → List V)
    (h : DescribesEulerTour G r L) :
    CondI G L ∧ CondII G L := by
  obtain ⟨hne, hdl, hc⟩ := follow_facts G r L h
  obtain ⟨_, es, htour⟩ := h
  obtain ⟨hloop, hcount⟩ := euler_counts G _ es htour
  have hcl := htour.1.2
  constructor
  · intro n
    unfold degree
    have := hcount (fun s => n ∈ s)
    rw [this]
    have hsplit := countP_split (prs (follow L r).1) hloop n
    rw [hsplit, countP_fst, countP_snd, count_tail_eq_dropLast _ hne hcl, hdl]
    omega
  · intro n m
    unfold edgeCount
    have := hcount (fun s => s = s(n, m))
    rw [this]
    by_cases hnm : n = m
    · subst hnm
      have h0 : (prs (follow L r).1).countP (fun p => decide (s(p.1, p.2) = s(n, n))) = 0 := by
        rw [List.countP_eq_zero]
        intro p hp
        have := hloop p hp
        obtain ⟨a, b⟩ := p
        simp only [decide_eq_true_eq, Sym2.eq_iff]
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact this (h1.trans h2.symm)
      have h00 : (prs (follow L r).1).count (n, n) = 0 := by
        rw [List.count_eq_zero]
        intro hp
        exact hloop _ hp rfl
      rw [h0]
      have := hc n n
      omega
    · rw [countP_edge _ hloop n m hnm, ← hc, ← hc]
      omega


lemma exists_last_split {α : Type} (p : α → Prop) [DecidablePred p] (Q : List α) (h : ∃ q ∈ Q, p q) :
    ∃ A q B, Q = A ++ q :: B ∧ p q ∧ ∀ x ∈ B, ¬ p x := by
  induction Q with
  | nil => simp at h
  | cons a Q ih =>
    by_cases h' : ∃ q ∈ Q, p q
    · obtain ⟨A, q, B, h1, h2, h3⟩ := ih h'
      exact ⟨a :: A, q, B, by simp [h1], h2, h3⟩
    · obtain ⟨q, hq, hp⟩ := h
      rcases List.mem_cons.1 hq with rfl | hq
      · exact ⟨[], q, Q, rfl, hp, fun x hx hpx => h' ⟨x, hx, hpx⟩⟩
      · exact absurd ⟨q, hq, hp⟩ h'

lemma prs_chain {V : Type} (ns : List V) : ∀ (A : List (V × V)) (q : V × V) (B : List (V × V)),
    prs ns = A ++ q :: B → (B = [] → ns.getLast? = some q.2) ∧ (∀ x B', B = x :: B' → x.1 = q.2) := by
  induction ns with
  | nil => intro A q B h; simp [prs] at h
  | cons a l ih =>
    cases l with
    | nil => intro A q B h; simp [prs_single] at h
    | cons b l =>
      intro A q B h
      rw [prs_cons_cons] at h
      cases A with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases l with
        | nil => simp [prs_single]
        | cons c l' =>
          rw [prs_cons_cons]
          simp
      | cons a' A' =>
        simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨_, h2⟩ := h
        obtain ⟨i1, i2⟩ := ih A' q B h2
        refine ⟨fun hb => ?_, i2⟩
        have := i1 hb
        simpa [List.getLast?_cons_cons] using this

lemma follow_facts2 {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]
    (G : Graph V E) (r : V) (L : V → List V) (h : DescribesEulerTour G r L) :
    (follow L r).1.head? = some r ∧
    (∀ a, ((prs (follow L r).1).filter (fun p => p.1 = a)).map Prod.snd = (L a).reverse) := by
  obtain ⟨hall, es, htour⟩ := h
  obtain ⟨h1, h2, h3, h4, h5⟩ := followAux_spec L (totalEntries L) r (fun _ => 0)
  refine ⟨h2, ?_⟩
  intro a
  have := h5 a
  have h6 := hall a
  unfold follow at h6 ⊢
  simp only [unused, h6, Nat.sub_self, List.take_zero, List.reverse_nil, List.append_nil, Nat.sub_zero, List.take_length] at this
  exact this.symm

theorem exists_last_exit_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (hconn : Connected G) (r : V) (L : V → List V)
    (h : DescribesEulerTour G r L) :
    (∀ n, n ≠ r → L n ≠ []) ∧
      ∀ S : Finset V, S.Nonempty → r ∉ S →
        ∃ n ∈ S, ∃ m, (L n).head? = some m ∧ m ∉ S := by
  have hI := (cond_i_ii_core G r L h).1
  have ha : ∀ n, n ≠ r → L n ≠ [] := by
    intro n hn hL
    have hdeg := hI n
    rw [hL] at hdeg
    obtain ⟨ns', es', hw, hh, hl⟩ := hconn n r
    have hes : es' ≠ [] := by
      intro he
      obtain ⟨hlen, _⟩ := hw
      rw [he] at hlen
      match ns', hlen, hh, hl with
      | [x], _, hh, hl => simp at hh hl; exact hn (hh.symm.trans hl)
    have h0 : 0 < es'.length := List.length_pos_iff.2 hes
    have hlen := hw.1
    have := hw.2 0 h0
    have hn0 : ns'[0]'(by omega) = n := by
      cases ns' with
      | nil => simp at hlen
      | cons x xs => simpa using hh
    rw [hn0] at this
    have hpos : 0 < degree G n := by
      unfold degree
      apply Finset.card_pos.2
      exact ⟨es'[0], by simp [this]⟩
    simp at hdeg
    omega
  refine ⟨ha, ?_⟩
  intro S hS hr
  obtain ⟨hhead, hfilt⟩ := follow_facts2 G r L h
  obtain ⟨hne, hdl, hc⟩ := follow_facts G r L h
  have hcl := h.2.choose_spec.1.2
  obtain ⟨s0, hs0⟩ := hS
  have hs0r : s0 ≠ r := fun e => hr (e ▸ hs0)
  have hex : ∃ q ∈ prs (follow L r).1, q.1 ∈ S := by
    have h1 := ha s0 hs0r
    have h2 : 0 < (prs (follow L r).1).countP (fun p => decide (p.1 = s0)) := by
      rw [countP_fst, hdl]
      exact List.length_pos_iff.2 h1
    obtain ⟨q, hq, hq2⟩ := List.countP_pos_iff.1 h2
    exact ⟨q, hq, by simpa using (by simpa using hq2 : q.1 = s0) ▸ hs0⟩
  obtain ⟨A, q, B, hsplit, hqS, hB⟩ := exists_last_split (fun q : V × V => q.1 ∈ S) _ hex
  obtain ⟨c1, c2⟩ := prs_chain _ A q B hsplit
  refine ⟨q.1, hqS, q.2, ?_, ?_⟩
  · have hf := hfilt q.1
    rw [hsplit, List.filter_append, List.filter_cons_of_pos (by simp), List.map_append, List.map_cons] at hf
    have hB' : B.filter (fun p => decide (p.1 = q.1)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := hB x hx
      simp only [decide_eq_true_eq]
      intro hx1
      exact this (hx1 ▸ hqS)
    rw [hB'] at hf
    have := congrArg List.getLast? hf
    rw [List.getLast?_reverse] at this
    simpa using this.symm
  · cases B with
    | nil =>
      have := c1 rfl
      rw [hhead] at hcl
      rw [← hcl] at this
      simp at this
      rw [← this]; exact hr
    | cons x B' =>
      rw [← c2 x B' rfl]
      exact hB x (by simp)

lemma sum_count_eq_length {V : Type} [Fintype V] [DecidableEq V] (l : List V) :
    ∑ b, l.count b = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have h1 : ∀ b, (x :: l).count b = l.count b + (if x = b then 1 else 0) := by
      intro b; by_cases h : x = b <;> simp [List.count_cons, h]
    simp only [h1, Finset.sum_add_distrib, ih, List.length_cons]
    simp

lemma sum_count_pair {V : Type} [Fintype V] [DecidableEq V] (l : List (V × V)) (a : V) :
    ∑ b, l.count (b, a) = l.countP (fun p => decide (p.2 = a)) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    obtain ⟨x1, x2⟩ := x
    have h1 : ∀ b, ((x1, x2) :: l).count (b, a) = l.count (b, a) + (if x2 = a ∧ x1 = b then 1 else 0) := by
      intro b; by_cases h : x2 = a ∧ x1 = b
      · obtain ⟨h2, h3⟩ := h; subst h2; subst h3; simp [List.count_cons]
      · have : ¬ ((x1, x2) = (b, a)) := by
          intro hh; apply h; rw [Prod.mk.injEq] at hh; exact ⟨hh.2, hh.1⟩
        simp [List.count_cons, h, this]
    simp only [h1, Finset.sum_add_distrib, ih, List.countP_cons]
    by_cases h : x2 = a <;> simp [h]

lemma sum_edgeCount {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] (G : Graph V E) (a : V) :
    ∑ b, edgeCount G a b = degree G a := by
  unfold edgeCount degree
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  generalize G.ends e = z
  induction z using Sym2.ind with
  | h x y =>
    by_cases hax : a = x
    · subst hax
      have : ∀ b, (s(a, y) = s(a, b)) ↔ y = b := fun b => Sym2.congr_right
      simp [this]
    · by_cases hay : a = y
      · subst hay
        have : ∀ b, (s(x, a) = s(a, b)) ↔ x = b := fun b => by rw [Sym2.eq_swap]; exact Sym2.congr_right
        simp [this]
      · have : ∀ b, ¬ (s(x, y) = s(a, b)) := by
          intro b hb
          rw [Sym2.eq_iff] at hb
          rcases hb with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hax h1.symm
          · exact hay h2.symm
        simp [this, Sym2.mem_iff, hax, hay]

lemma in_eq_out {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (L : V → List V) (h1 : CondI G L) (h2 : CondII G L) (a : V) :
    ∑ b, (L b).count a = (L a).length := by
  have e1 := sum_edgeCount G a
  have e2 : ∑ b, edgeCount G a b = ∑ b, ((L b).count a + (L a).count b) :=
    Finset.sum_congr rfl (fun b _ => h2 a b)
  rw [Finset.sum_add_distrib, sum_count_eq_length] at e2
  have := h1 a
  omega

lemma count_tail_dropLast {V : Type} [DecidableEq V] (ns : List V) (x y : V) (hx : ns.head? = some x)
    (hy : ns.getLast? = some y) (a : V) :
    ns.tail.count a + (if x = a then 1 else 0) = ns.dropLast.count a + (if y = a then 1 else 0) := by
  obtain ⟨x', rest, rfl⟩ : ∃ x' rest, ns = x' :: rest := by
    cases ns with
    | nil => simp at hx
    | cons x' rest => exact ⟨x', rest, rfl⟩
  have hne : (x' :: rest) ≠ [] := by simp
  have e1 : (x' :: rest).count a = (x' :: rest).dropLast.count a + (if y = a then 1 else 0) := by
    have hy' : (x' :: rest).getLast hne = y := by
      rw [List.getLast?_eq_getLast_of_ne_nil hne] at hy; simpa using hy
    conv_lhs => rw [← List.dropLast_append_getLast hne]
    rw [List.count_append, hy']
    by_cases h : y = a <;> simp [List.count_cons, h]
  have e2 : (x' :: rest).count a = rest.count a + (if x' = a then 1 else 0) := by
    by_cases h : x' = a <;> simp [List.count_cons, h]
  simp only [List.head?_cons, Option.some.injEq] at hx
  subst hx
  simp only [List.tail_cons]
  omega

theorem returns_to_root_core {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (r : V) (L : V → List V) (h1 : CondI G L) (h2 : CondII G L) :
    (follow L r).1.getLast? = some r ∧ (follow L r).2 r = (L r).length ∧
      ∀ m, r ∉ unused L (follow L r).2 m := by
  obtain ⟨hne, hhead, ht3, ht4, -⟩ := followAux_spec L (totalEntries L) r (fun _ => 0)
  have hbd := followAux_bound L (totalEntries L) r (fun _ => 0) (fun a => Nat.zero_le _)
  have hlast : ∃ w, (follow L r).1.getLast? = some w := by
    unfold follow
    cases hh : (followAux L (totalEntries L) r fun _ => 0).1 with
    | nil => exact absurd hh hne
    | cons x l => exact ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hlast
  have hend := followAux_end L (totalEntries L) r (fun _ => 0) (by simp [totalEntries]) w hw
  have key : ∀ a, ∑ b, (unused L (follow L r).2 b).count a + (if w = a then 1 else 0) =
      (unused L (follow L r).2 a).length + (if r = a then 1 else 0) := by
    intro a
    have hin : ∑ b, (L b).count a = ∑ b, (unused L (follow L r).2 b).count a + (prs (follow L r).1).countP (fun p => decide (p.2 = a)) := by
      rw [← sum_count_pair, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      have := ht4 b a
      simp only [unused, Nat.sub_zero, List.take_length] at this
      unfold follow
      simpa [unused] using this
    rw [countP_snd] at hin
    have hio := in_eq_out G L h1 h2 a
    have hcl := count_tail_dropLast (follow L r).1 r w hhead hw a
    have hlen : (unused L (follow L r).2 a).length = (L a).length - (follow L r).2 a := by
      simp [unused]
    have hb := hbd a
    have h3 := ht3 a
    unfold follow at *
    simp only [zero_add] at h3
    omega
  have hUw : (unused L (follow L r).2 w).length = 0 := by
    have : (L w).length ≤ (follow L r).2 w := hend
    have hb := hbd w
    unfold follow at *
    simp [unused]
    omega
  have hrw : r = w := by
    have := key w
    rw [hUw] at this
    by_contra hh
    simp [hh] at this
  subst hrw
  have hk := key r
  simp only [hUw, if_true] at hk
  have hz : ∑ b, (unused L (follow L r).2 b).count r = 0 := by omega
  refine ⟨hw, ?_, ?_⟩
  · have hb := hbd r
    have : (L r).length ≤ (follow L r).2 r := hend
    unfold follow at *
    omega
  · intro m hm
    have := (Finset.sum_eq_zero_iff.1 hz) m (Finset.mem_univ _)
    exact (List.count_eq_zero.1 this) hm


end ChinesePostman.NextNode

open ChinesePostman.NextNode


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : ChinesePostman.NextNode.Graph V E) (r : V) (L : V → List V) (h1 : CondI G L) (h2 : CondII G L) :
    (follow L r).1.getLast? = some r ∧ (follow L r).2 r = (L r).length ∧
      ∀ m, r ∉ unused L (follow L r).2 m := by
  exact returns_to_root_core G r L h1 h2
